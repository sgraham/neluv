import glob
import importlib
import sys

from luv_lark import Lark_StandAlone, PythonIndenter, Tree, Transformer, v_args
import last

this_module = sys.modules[__name__]

_TEST_CODE2 = '''
if x > 2:
  print(4)
else:
  print(5)

def wee():
  return true
  return false
  return null

def int waa():
  return 45

struct Wee:
  i64 a
  i64 b

union FloatOrInt:
  i64 i
  f64 f

preproc:  // Python blocks that act on current AST
  def increment(a, amount):
    node = luvast.Assign(luvast.Id(a),
                         luvast.Add(luvast.Id(a), amount))
    inject_statement(node)
    for x in node:
      print(x)

x = 0

preproc:
  increment(x, 4)

print(x)

x = #{math.pi}

#["x"] = 44
'''

# Suite of `macro` would be Python
# But that means that it can't be parsed purely by a python exec() as
# there's no way to escape back.
# Could parse some janky subset with an augmented python grammar that has
# escapes
# Or only do a procedural version where you need to construct the new AST
# manually in Python code.
# Maybe something that re-invokes the luv parser taking a string is fine r'''?.
# But need to sub back in args from python too, hmm.
# Could use inspect.currentframe().f_back.f_locals
# Could also use fr''', but that means that it'll be python->string->luv which
# might be tedious, depending on what you're substituting in.
# Could start with the manual version and see how it goes? Will be verrry
# painful (and fragile) to write macros that manually manipulate AST objects though.
#macro printx:
#    for item in printx.arguments:
#        yield [|
#            UnityEngine.Debug.Log($item)
#        |]
#

def Macro_printx(printx):
  for item in printx.arguments:
    node = last.String(item)
    yield last.parse(r'''
  Engine.Debug.Log($node)
''')




# Need some way for the macro code to get access to scope knowledge to look up
# type of variables, etc.
_TEST_CODE = '''
def funcy(int x):
  print(x)
x=1

A a
int c = 5
A d = stuff()
e = things()
X.Y z
X.Y.Z w = 0
X.Y.Z.W q = 1

funcy(x)
'''

_PREPROC_GLOBALS = {}
_PREPROC_LOCALS = {}
_MACROS = {}
_KEYWORDS = {
  'auto': last.Type('auto'),
  'bool': last.Type('bool'),
  'int': last.Type('int'),
  'void': last.Type('void'),
}


def load_builtin_macros():
  for x in ["print"]:
    mod = importlib.import_module(x)
    if _MACROS.get(x):
      raise RuntimeError('conflicting definition of builtin macro for %s' % x)
    _MACROS[x] = getattr(mod, x)

class CompilerContext:
  def type_(self, t):
    return t.name

  def param(self, p):
    if isinstance(p, last.TypedParam):
      return '%s %s' % (self.type_(p.type), p.name)
    else:
      assert False, "unhandled param %s" % p

  def return_type_of_block(self, block):
    for s in block.entries:
      #if isinstance(s, last.Return):
        #pass
      pass
    return _KEYWORDS['void']

  def definition(self, d):
    if isinstance(d, last.FuncDef):
      # TODO: need stack of in-scope vars with types (upvals, globals, etc too)
      return_type = self.return_type_of_block(d.body)
      if d.type != _KEYWORDS['auto']:
        if d.type != return_type:
          raise TypeError('%s specified as returning "%s" but returns "%s"' % (
            d.name, self.type_(d.type), self.type_(return_type)))
      params = ','.join(self.param(p) for p in d.params)
      if not params:
        params = self.type_(_KEYWORDS['void'])
      res = 'static %s %s(%s) {' % (self.type_(return_type), d.name, params)
      res += self.block(d.body)
      return res + '}'
    else:
      assert False, "unhandled definition %s" % d

  def lval(self, v):
    if isinstance(v, last.Ident):
      return v.name
    else:
      assert False, "unhandled lval %s" % v

  def expr(self, e):
    if isinstance(e, last.Number):
      return e.value
    elif isinstance(e, last.Ident):
      return e.name
    elif isinstance(e, last.FuncCall):
      # The parser distinguishes between func and macro if there's a : body, but
      # otherwise they look identical, so check macros before emitting a normal
      # runtime function call.
      if isinstance(e.func, last.Ident) and _MACROS.get(e.func.name):
        mac = _MACROS.get(e.func.name)
        result = mac(self, e.args, None)  # None is body
        return result
      else:
        funcval = self.expr(e.func)
        return '%s(%s)' % (funcval, ','.join(self.expr(a) for a in e.args))
    elif isinstance(e, last.MacroCallWithBlock):
      assert isinstance(e.func, last.FuncCall)
      if not isinstance(e.func.func, last.Ident):
        raise TypeError('macro invocation "%s" expected to only be a name' % e.func.func)
      mac = _MACROS.get(e.func.func.name)
      if not mac:
        raise TypeError('macro "%s" not found' % e.func.func.name)
      return mac(self, e.func.args, e.body)
    else:
      assert False, "unhandled expr %s" % e

  def stmt(self, s):
    if isinstance(s, last.Assign):
      return '%s = %s;' % (self.lval(s.lhs), self.expr(s.rhs))
    else:
      return self.expr(s) + ';'

  def get_type(self, expr):
    if isinstance(expr, last.Number):
      return _KEYWORDS['int']
    else:
      assert False, "unhandled get_type %s" % expr

  def find_local_decls(self, block):
    assignments = {}
    for s in block.entries:
      if isinstance(s, last.Assign):
        if isinstance(s.lhs, last.Ident):
          rhs_type = self.get_type(s.rhs)
          if not assignments.get(s.lhs.name, None):
            assignments[s.lhs.name] = rhs_type
          else:
            prev_lhs_type = assignments[s.lhs.name]
            if rhs_type != prev_lhs_type:
              raise TypeError('%s was "%s", but now "%s"' % (
                s.lhs.var.name, prev_lhs_type, rhs_type))
    return assignments

  def block(self, block):
    res = ''
    for n,t in self.find_local_decls(block).items():
      typename = self.type_(t)
      res += '%s %s = (%s){0};' % (typename, n, typename)
    return res + '\n'.join(self.stmt(s) for s in block.entries)

  def goes_in_main(self, x):
    #return not (isinstance(x, last.FuncDef) or isinstance(x, last.PreProc))
    return not (isinstance(x, last.FuncDef))

  def codegen(self, toplevel):
    res = ''

    top, in_main = [], []
    for x in toplevel.body.entries:
      (in_main if self.goes_in_main(x) else top).append(x)
    in_main = last.Block(in_main)

    res = '#include <stdio.h>\n\n'

    for t in top:
      res += self.definition(t)

    res += 'int main(void) {'

    res += self.block(in_main)
    res += '}'
    return res

class ToAst(Transformer):
  def DEC_NUMBER(self, n):
    #print('DEC_NUMBER', n, file=sys.stderr)
    return int(n)

  def NAME(self, n):
    #print('NAME', n, file=sys.stderr)
    return str(n)

  def funccall(self, children):
    return last.FuncCall(children[0], children[1] if len(children) > 1 else [])

  def arguments(self, children):
    return children

  def number(self, children):
    return last.Number(children[0])

  def ident(self, children):
    x = _KEYWORDS.get(children[0], None)
    if x:
      return x
    return last.Ident(children[0])

  def dotted_name(self, children):
    # ident rather than Ident to get keyword if actually undotted.
    # This handles `int x`, but not `A.int x` which I think is what I want.
    if len(children) == 1:
      return self.ident(children)
    cur = last.Ident(children[-1])
    for i in range(len(children) - 2, -1, -1):
      cur = last.FieldReference(children[i], cur)
    return cur

  def typed_uninit_var_decl(self, children):
    return last.VarDecl(children[0], children[1], None)

  def typed_or_init_var_decl(self, children):
    if len(children) > 2:
      return last.VarDecl(children[0], children[1], children[2])
    else:
      return last.VarDecl(None, children[0], children[1])

  def macro_with_block_stmt(self, children):
    return last.MacroCallWithBlock(children[0], children[1])

  def returntype(self, children):
    assert isinstance(children[0], last.Type)
    return children[0]

  def name(self, children):
    return children[0]

  def assign(self, children):
    return last.Assign(children[0], children[1])

  def funcdef(self, children):
    x = children[0]
    type = children.pop(0) if isinstance(x, last.Type) else _KEYWORDS['auto']
    name = children.pop(0)
    x = children[0]
    params = children.pop(0) if isinstance(x, list) else []
    body = children.pop(0)
    return last.FuncDef(type, name, params, body)

  def typedparam(self, children):
    return last.TypedParam(children[0], children[1])

  def parameters(self, children):
    return children

  def suite(self, children):
    return last.Block(children)

  '''
  def preproc_stmt(self, children):
    result = []
    def indented_lines(ppl, indent):
      for c in ppl:
        if isinstance(c, Tree) and c.data == 'preproc_line':
          indented_lines(c.children, indent + '  ')
        else:
          result.append(indent[2:] + c.value)
    indented_lines(children, '')
    return last.PreProc(result)
  '''

  def expr_stmt(self, children): return children[0]
  def assign_stmt(self, children): return children[0]

  def start(self, children):
    return last.TopLevel(last.Block(children))

def parse_tests(parser):
  import pprint
  for pt in glob.glob('test/parse/*.luv'):
    pt = pt.replace('\\', '/')
    with open(pt, 'r') as f:
      source, _, expected = f.read().partition('---\n')
    expected = expected.rstrip('\n')
    tree = parser.parse(source)
    ast = ToAst(visit_tokens=True).transform(tree)
    got = pprint.pformat(ast)
    if expected != got:
      print(pt)
      print('--- EXPECTED')
      print("%s" % expected)
      print('--- GOT')
      print("%s" % got)
      raise SystemExit(1)
    else:
      print('OK: %s' % pt)

def main():
  parser = Lark_StandAlone(postlex=PythonIndenter())

  load_builtin_macros()
  #print(_MACROS)

  if len(sys.argv) == 2 and sys.argv[1] == 'test':
    parse_tests(parser)
  else:
    tree = parser.parse(_TEST_CODE)
    print(tree.pretty(), file=sys.stderr)

    ast = ToAst(visit_tokens=True).transform(tree)
    import pprint
    pprint.pprint(ast, stream=sys.stderr)

    cctx = CompilerContext()
    print(cctx.codegen(ast))

    '''
    class MacroContext:
      def __init__(self):
        self.arguments = ['a', 'b', 'c']
    ctx = MacroContext()
    for x in Macro_printx(ctx):
      print('yielded', x)
    '''

if __name__ == '__main__':
  main()
