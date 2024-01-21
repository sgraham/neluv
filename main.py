import dataclasses
import glob
import importlib
import os
import pprint
import subprocess
import sys

#from luv_lark import Lark_StandAlone, PythonIndenter, Tree, Transformer, v_args, UnexpectedToken, logger
from lark import Lark, Tree, Transformer, v_args, UnexpectedToken, logger, Visitor
from lark.indenter import PythonIndenter

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

def add_meta(f, data, children, meta):
  ret = f(children)
  if not meta.empty and isinstance(ret, last.AstNode):
    ret.line = meta.line
    ret.column = meta.column
  return ret

@v_args(wrapper=add_meta)
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

  def const_true(self, children):
    return _KEYWORDS['true']

  def const_false(self, children):
    return _KEYWORDS['false']

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

  def if_stmt(self, children):
    return last.If(children[0], children[1], children[2], children[3])

  def elif_(self, children):
    return last.Elif(children[0], children[1])

  def elifs(self, children):
    return children

  def getitem(self, children):
    return last.GetItem(children[0], children[1])

  def structdef(self, children):
    return last.Struct(children[0], children[1])

  def uniondef(self, children):
    return last.Union(children[0], children[1])

  def struct_union_types(self, children):
    for x in children:
      assert isinstance(x, last.TypedVar)
    return children

  def returntype(self, children):
    assert children[0] is None or isinstance(children[0], last.Type)
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
                       propagate_positions=True,
                       #cache=True,
                       #debug=True,
                       strict=True)

  def parse(self, code):
    try:
      return self.parser.parse(code)
    except UnexpectedToken as err:
      return Tree('error', children=[last.ParseError(err.line, err.column, err.token)])

class Typer:
  def __init__(self):
    pass

class Compiler:
  def __init__(self, filename, error_at=None):
    self.globals = {}
    self.filename = filename
    def default_error_at(node, msg):
      print('%s:%d:%d:error: %s' % (self.filename, node.line, node.column, msg), file=sys.stderr)
      sys.exit(1)
    self.error_at = error_at or default_error_at

  class FuncSymTabVisit:
    def __init__(self, func, parent):
      self.func = func
      self.parent = parent

    def visit_VarDecl(self, node):
      x = self.func.symtab.get(node.name)
      if x:
        self.parent.error_at(node, 'redefinition of "%s" in "%s"' % (node.name, self.func.name))
      self.func.symtab[node.name] = node

  def build_func_symbol_table(self, func):
    self.visit(self.FuncSymTabVisit(func, self), func)

  def visit(self, visitor, node):
    x = getattr(visitor, 'visit_' + node.__class__.__name__, None)
    if x:
      x(node)
    for f in dataclasses.fields(node):
      field = getattr(node, f.name)
      if isinstance(field, last.AstNode):
        self.visit(visitor, field)
      elif isinstance(field, list):
        for lx in field:
          if isinstance(lx, last.AstNode):
            self.visit(visitor, lx)

  def build_symbol_table(self, ast):
    assert isinstance(ast, last.TopLevel), ast
    for tl in ast.body.entries:
      if (isinstance(tl, last.TypedVar) or
          isinstance(tl, last.FuncDef) or
          isinstance(tl, last.VarDecl)):
        if self.globals.get(tl.name):
          self.error_at(tl, 'redefinition at global scope of "%s"' % tl.name)
        self.globals[tl.name] = tl
        if isinstance(tl, last.FuncDef):
          self.build_func_symbol_table(tl)
      else:
        self.error_at(tl, 'syntax error %s' % tl)

  def infer_types(self, ast):
    # push all FuncDefs with auto return on to queue
    # pop, if auto, try to determine type
    # return types
    pass

  def get_c_type(self, node):
    if node == _KEYWORDS['i32']:
      return 'int32_t'
    print('GET_C_TYPE', node)
    return '???'

  def get_safe_c_name(self, luv_name):
    # TODO
    return luv_name

  def expr(self, node):
    if isinstance(node, last.Ident):
      return self.get_safe_c_name(node.name)
    elif isinstance(node, last.Number):
      return str(node.value)  # TODO, safe-ize this, incl floats, etc.
    elif isinstance(node, last.CompExpr):
      assert len(node.chain) == 3, "todo chained"
      # TODO: passing op right through
      return '(%s) %s (%s)' % (
          self.expr(node.chain[0]), node.chain[1].name, self.expr(node.chain[2]))
    elif isinstance(node, last.FuncCall):
      result = self.expr(node.func)
      result += '('
      result += ','.join(self.expr(x) for x in node.args)
      result += ')'
      return result
    elif isinstance(node, last.BinaryExpr):
      # TODO: passing op right through
      return '(%s) %s (%s)' % (self.expr(node.lhs), node.op.name, self.expr(node.rhs))
    else:
      raise RuntimeError("unhandled expr node %s" % node)

  def stmt(self, node):
    if isinstance(node, last.Block):
      result = '{'
      for x in node.entries:
        result += self.stmt(x)
      result += '}'
      return result
    elif isinstance(node, last.If):
      result = 'if ('
      result += self.expr(node.cond)
      result += ')'
      result += self.stmt(node.body)
      for el in node.elifs:
        result += 'else if ('
        result += self.expr(el.cond)
        result += ')'
        result += self.stmt(el.body)
      if node.els:
        result += self.stmt(node.els)
      return result
    elif isinstance(node, last.Return):
      result = 'return'
      if node.value:
        result += ' ' + self.expr(node.value) + ';'
      return result
    elif isinstance(node, last.Assign):
      return '%s = %s;' % (self.expr(node.lhs), self.expr(node.rhs))
    elif isinstance(node, last.VarDecl):
      if node.init:
        return '%s = %s;' % (self.get_safe_c_name(node.name), self.expr(node.init))
      else:
        return ''
    else:
      return self.expr(node) + ';'

  def codegen_FuncDef(self, func):
    params = []
    for p in func.params:
      params.append('%s %s' % (self.get_c_type(p.type), self.get_safe_c_name(p.name)))
    if not params:
      params = 'void'
    else:
      params = ','.join(params)
    fname = self.get_safe_c_name(func.name)
    if fname == 'main':
      rtype = 'int'
    else:
      rtype = self.get_c_type(func.rtype)
    result = '%s %s(%s){' % (rtype, fname, params)
    for n,loc in func.symtab.items():
      result += '%(type)s %(name)s = (%(type)s){0};' % {
          'type': self.get_c_type(loc.type),
          'name': self.get_safe_c_name(loc.name)}
    result += self.stmt(func.body)
    result += '}'
    return result

  def compile(self, outfn):
    with open(outfn, 'w') as f:
      f.write(r'''
#include <stdint.h>
#include <stdio.h>
static void printint(int x) {
  printf("%d\n", x);
}
''')
      for n,obj in self.globals.items():
        if isinstance(obj, last.FuncDef):
          f.write(self.codegen_FuncDef(obj))

def test_contents(fn):
  with open(fn, 'r') as f:
    source, _, after = f.read().partition('\n---\n')
  after = after.rstrip('\n')
  return source + '\n', after

def dyibicc(c_file):
  compiler_path = r'../dyibicc/out/wd/dyibicc.exe'
  proc = subprocess.run([compiler_path, c_file], capture_output=True, text=True)
  if proc.returncode != 0:
    print('---STDOUT')
    print(proc.stdout, file=sys.stderr)
    print('---STDERR')
    print(proc.stderr, file=sys.stderr)
    raise RuntimeError('compile failed')
  return proc.stdout.rstrip('\n')

def do_tests(parser, test_list):
  if not test_list:
    test_list = sorted(glob.glob('test/**/*.luv', recursive=True))

  disabled_list = []
  passed_list = []
  err = None
  def tt_error_at(node, msg):
    err['node'] = node
    err['msg'] = msg

  for t in test_list:
    if '.disabled.' in t:
      disabled_list.append(t)
      continue
    t = t.replace('\\', '/')
    source, expected = test_contents(t)
    tree = parser.parse(source)
    #print(tree.pretty())
    ast = ToAst().transform(tree)
    if t.startswith('test/parse'):
      got = pprint.pformat(ast)
    elif t.startswith('test/type'):
      err = {}
      c = Compiler(t, error_at=tt_error_at)
      c.build_symbol_table(ast)
      c.infer_types(ast)
      got = '%s:%d:%d:%s' % (t, err['node'].line, err['node'].column, err['msg'])
      expected = expected.lstrip('!\n')
    elif t.startswith('test/run'):
      c = Compiler(t)
      c.build_symbol_table(ast)
      c.infer_types(ast)
      c_file = os.path.splitext(t)[0] + '.c'
      c.compile(c_file)
      got = dyibicc(c_file)

    if expected != got:
      print(t)
      print('--- EXPECTED')
      print("%s" % expected)
      print('--- GOT')
      print("%s" % got)
      raise SystemExit(1)
    else:
      passed_list.append(t)
      sys.stdout.write('.')
      sys.stdout.flush()

  print()
  print('%d tests OK' % len(passed_list))
  print('%d tests disabled' % len(disabled_list))

def main():
  parser = Parser()

  load_builtin_macros()
  #print(_MACROS)

  if len(sys.argv) >= 2 and sys.argv[1] == 'test':
    do_tests(parser, sys.argv[2:])
  else:
    source, _ = test_contents(sys.argv[1])
    tree = parser.parse(source + '\n')
    #print(tree.pretty(), file=sys.stderr)

    ast = ToAst().transform(tree)
    import pprint
    pprint.pprint(ast, stream=sys.stderr)

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
