import logging

import glob
import importlib
import sys

#from luv_lark import Lark_StandAlone, PythonIndenter, Tree, Transformer, v_args, UnexpectedToken, logger
from lark import Lark, Tree, Transformer, v_args, UnexpectedToken, logger
from lark.indenter import PythonIndenter

logger.setLevel(logging.DEBUG)
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
  'byte': last.Type('u8'),
  'double': last.Type('f64'),
  'f16': last.Type('f16'),
  'f32': last.Type('f32'),
  'f64': last.Type('f64'),
  'float': last.Type('f32'),
  'i16': last.Type('i16'),
  'i32': last.Type('i32'),
  'i64': last.Type('i64'),
  'i8': last.Type('i8'),
  'int': last.Type('i32'),
  'u16': last.Type('u16'),
  'u32': last.Type('u32'),
  'u64': last.Type('u64'),
  'u8': last.Type('u8'),
  'void': last.Type('void'),

  'false': last.Const('false'),
  'null': last.Const('null'),
  'true': last.Const('true'),
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

  def STRING(self, v):
    return v[1:-1]

  def __default_token__(self, tok):
    return last.Op(tok.value)

  def funccall(self, children):
    return last.FuncCall(children[0], children[1] or [] if len(children) > 1 else [])

  def arguments(self, children):
    return children

  def number(self, children):
    return last.Number(children[0])

  def string(self, children):
    return last.String(children[0])

  def ident(self, children):
    x = _KEYWORDS.get(children[0], None)
    if x:
      return x
    return last.Ident(children[0])

  def const_null(self, children):
    return _KEYWORDS['null']

  def name_with_package(self, children):
    cur = last.Ident(children[-1])
    for i in range(len(children) - 2, -1, -1):
      cur = last.PackageReference(children[i], cur)
    return cur

  def getattr(self, children):
    return last.GetAttr(children[0], children[1])

  def arith_expr(self, children):
    return last.BinaryExpr(children[0], children[2], children[1])

  def term(self, children):
    return last.BinaryExpr(children[0], children[2], children[1])

  def factor(self, children):
    if len(children) == 2:
      return last.UnaryExpr(children[0], children[1])
    else:
      return last.BinaryExpr(children[0], children[2], children[1])

  def comparison(self, children):
    assert (len(children) - 3) % 2 == 0
    return last.CompExpr(children)

  def comp_op(self, children):
    return children[0]

  def slice_decl(self, children):
    return last.SliceDecl(children[0])

  def fixed_array_decl(self, children):
    return last.FixedArrayDecl(size=children[0], base=children[1])

  def pointer_decl(self, children):
    return last.PointerDecl(children[0])

  def type_for_var(self, children):
    return children[0]

  def typed_var(self, children):
    return last.TypedVar(children[0], children[1])

  def var_decl_init(self, children):
    if len(children) == 1:
      assert isinstance(children[0], last.TypedVar)
      return children[0]
    else:
      return last.VarDecl(children[0].type, children[0].name, children[1])

  def macro_with_block_stmt(self, children):
    return last.MacroCallWithBlock(children[0], children[1])

  def return_stmt(self, children):
    return last.Return(children[0])

  def pass_stmt(self, children):
    return last.Pass()

  def for_stmt(self, children):
    return last.For(children[0], children[1], children[2], children[3])

  def getitem(self, children):
    return last.GetItem(children[0], children[1])

  def structdef(self, children):
    return last.Struct(children[0], children[1])

  def struct_union_types(self, children):
    for x in children:
      assert isinstance(x, last.TypedVar)
    return children

  def returntype(self, children):
    #assert isinstance(children[0], last.Type)
    return children[0]

  def name(self, children):
    return children[0]

  def assign(self, children):
    return last.Assign(children[0], children[1])

  def funcdef(self, children):
    if len(children) == 2:
      return last.FuncDef(_KEYWORDS['auto'], children[0], [], children[1])
    elif len(children) == 3:
      if isinstance(children[0], last.Type):
        return last.FuncDef(children[0], children[1], [], children[2])
      else:
        return last.FuncDef(_KEYWORDS['auto'], children[0], children[1], children[2])
    elif len(children) == 4:
      return last.FuncDef(children[0] or _KEYWORDS['auto'],
                          children[1],
                          children[2] or [],
                          children[3])
    assert False, "unhandled case in funcdef"

  def funcdecl(self, children):
    type = children[0] or _KEYWORDS['auto']
    params = children[1]
    return last.FuncType(base=None, rtype=type, params=params)

  def parameter_types(self, children):
    return children

  def typedparam(self, children):
    return last.TypedVar(children[0], children[1])

  def parameters(self, children):
    return children

  def suite(self, children):
    return last.Block(children)

  def error(self, children):
    return children[0]

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

class Parser:
  def __init__(self):
    #self.parser = Lark_StandAlone(postlex=PythonIndenter())
    # TODO: Bailed on LR(1) due to var decl syntax:
    # e.g.
    #   def x(int, float) my_function_pointer
    #   // a pointer to a function returning `x` taking (int, float)
    # vs.
    #   def x(int x, float y):
    #   // the start of a function definition
    #     ...
    self.parser = Lark(grammar=open('luv.lark').read(),
                       parser='earley',
                       lexer='basic',
                       postlex=PythonIndenter(),
                       #cache=True,
                       #debug=True,
                       strict=True)

  def parse(self, code):
    try:
      return self.parser.parse(code)
    except UnexpectedToken as err:
      return Tree('error', children=[last.ParseError(err.line, err.column, err.token)])

def parse_tests(parser):
  import pprint
  for pt in sorted(glob.glob('test/parse/**/*.luv', recursive=True)):
    pt = pt.replace('\\', '/')
    with open(pt, 'r') as f:
      source, _, expected = f.read().partition('---\n')
    expected = expected.rstrip('\n')
    tree = parser.parse(source)
    #print(tree.pretty())
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
  parser = Parser()

  load_builtin_macros()
  #print(_MACROS)

  if len(sys.argv) == 2 and sys.argv[1] == 'test':
    parse_tests(parser)
  else:
    contents = open(sys.argv[1]).read()
    source, _, backmatter = contents.partition('\n---\n')
    tree = parser.parse(source + '\n')
    #print(tree.pretty(), file=sys.stderr)

    ast = ToAst(visit_tokens=True).transform(tree)
    import pprint
    pprint.pprint(ast, stream=sys.stderr)

    #cctx = CompilerContext()
    #print(cctx.codegen(ast))

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
