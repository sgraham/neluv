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
    assert (len(children) - 3) % 2 == 0
    return last.Expr(children)

  def term(self, children):
    assert (len(children) - 3) % 2 == 0
    return last.Expr(children)

  def factor(self, children):
    if len(children) == 2:
      return last.UnaryExpr(children[0], children[1])
    else:
      assert (len(children) - 3) % 2 == 0
      return last.Expr(children)

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
      return last.VarDecl(children[0].type, children[0].name, None)
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
  def __init__(self, filename, ast_root, error_at=None):
    self.globals = {}
    self.filename = filename
    def default_error_at(node, msg):
      print('%s:%d:%d:error: %s' % (self.filename, node.line, node.column, msg), file=sys.stderr)
      sys.exit(1)
    self.error_at = error_at or default_error_at

    self.ast_root = ast_root
    self.find_globals()
    self.build_function_symtabs()
    self.hoist_nested_functions()
    self.infer_types()

    self.current_function = None

  class FuncSymTabVisit:
    def __init__(self, func, parent):
      self.func = func
      self.parent = parent
      for p in func.params:
        assert isinstance(p, last.TypedVar)
        func.symtab[p.name] = last.FuncSymTabEntry(p.type, p, is_func_param=True)

    def visit_VarDecl(self, node):
      x = self.func.symtab.get(node.name)
      if x:
        self.parent.error_at(node, 'redefinition of "%s" in "%s"' % (node.name, self.func.name))
      self.func.symtab[node.name] = last.FuncSymTabEntry(node.type, node, is_declared_local=True)

    def visit_Assign(self, node):
      if isinstance(node.lhs, last.Ident):  # TODO: Is this sufficient?
        if not self.func.symtab.get(node.lhs.name):
          self.func.symtab[node.lhs.name] = last.FuncSymTabEntry(
              self.parent.expr_type(self.func, node.rhs), node, is_declared_local=True)

  def build_function_symtabs(self):
    for f in self.find_func_defs(self.ast_root):
      self.visit(self.FuncSymTabVisit(f, self), f.body, do_not_cross_types=[last.FuncDef])

  def visit(self, visitor, node, do_not_cross_types=None):
    x = getattr(visitor, 'visit_' + node.__class__.__name__, None)
    if x:
      x(node)

    if do_not_cross_types:
      for dnct in do_not_cross_types:
        if isinstance(node, dnct):
          return

    for f in dataclasses.fields(node):
      field = getattr(node, f.name)

      if isinstance(field, last.AstNode):
        self.visit(visitor, field, do_not_cross_types)
      elif isinstance(field, list):
        for lx in field:
          if isinstance(lx, last.AstNode):
            self.visit(visitor, lx, do_not_cross_types)

  def insert_global_or_error(self, node):
    name = node.name
    if self.globals.get(name):
      self.error_at(node, 'redefinition at global scope of "%s"' % name)
    self.globals[name] = node

  def find_globals(self):
    assert isinstance(self.ast_root, last.TopLevel), self.ast_root

    for tl in self.ast_root.body.entries:
      if (isinstance(tl, last.FuncDef) or
          isinstance(tl, last.VarDecl)):
        self.insert_global_or_error(tl)
      elif isinstance(tl, last.Assign) and isinstance(tl.lhs, last.Ident):
        # Handled below.
        pass
      else:
        self.error_at(tl, 'syntax error %s' % tl)

    for i, tl in enumerate(self.ast_root.body.entries):
      if isinstance(tl, last.Assign) and isinstance(tl.lhs, last.Ident):
        # Turn simple Assign into VarDecl at global scope
        x = last.VarDecl(self.expr_type(None, tl.rhs), tl.lhs.name, tl.rhs)
        x.copy_meta(tl)
        self.ast_root.body.entries[i] = x
        self.insert_global_or_error(x)

  def find_func_defs(self, start, top_level_only=False):
    class FindFuncDef:
      def __init__(self): self.result = []
      def visit_FuncDef(self, node): self.result.append(node)
    finder = FindFuncDef()
    self.visit(finder, start, do_not_cross_types=[last.FuncDef] if top_level_only else None)
    return finder.result

  def replace_ident_references(self, start, old, new):
    class ReplaceIdents:
      def visit_Ident(self, v):
        if v.name == old:
          v.name = new
    self.visit(ReplaceIdents(), start)

  def find_upvals(self, func, lexical_func_stack):
    class FindIdents:
      def __init__(self): self.idents = []
      def visit_Ident(self, v): self.idents.append(v)
    finder = FindIdents()
    # We do have to decend into sub-functions here (i.e. not just the strict
    # body of this function) because if a further nested function refers to
    # something above this function, we need to request it from the parent.
    self.visit(finder, func.body)

    # Find all the identifiers referenced in this function that refer to a
    # parent scope. Add entries to this function's symtab (marking them as
    # upval) and also return them.
    to_bind = {}
    for i in finder.idents:
      for f in reversed(lexical_func_stack):
        if in_upper := f.symtab.get(i.name):
          if f != func:
            #print('upval req for %s of %s, found in %s' % (i.name, func.name, f.name))
            fste = last.FuncSymTabEntry(in_upper.type, in_upper.ref_node, is_upval=True)
            func.symtab[i.name] = fste
            to_bind[i.name] = fste
          else:
            break
    return to_bind

  class Hoister:
    def __init__(self, parent):
      self.parent = parent
      self.add_to_toplevel = []
      self.cur_func_stack = []

    def hoist(self, root):
      func_defs = self.parent.find_func_defs(root, top_level_only=True)
      for nested in func_defs:
        if self.cur_func_stack:
          cur = self.cur_func_stack[-1]
          # Give the hoisted function a unique-ish name.
          old_name = nested.name
          new_name = old_name + '$%s' % cur.name
          nested.name = new_name

          to_bind = self.parent.find_upvals(nested, self.cur_func_stack + [nested])
          if to_bind:
            uvb = last.UpvalBindings(to_bind, new_name)
            cur.upval_bindings[new_name] = uvb
            nested.params.insert(0,
                last.TypedVar(last.PointerDecl(last.Type(uvb.struct_name)), '$up'))

          # Remove the declaration from the body of the current function,
          # replacing calls to it.
          cur.body.entries.remove(nested)  # TODO: prob unnecessary O(n)
          self.add_to_toplevel.append(nested)
          self.parent.replace_ident_references(cur.body, old_name, new_name)
          #pprint.pprint(cur_func)

        self.cur_func_stack.append(nested)
        self.hoist(nested.body)
        self.cur_func_stack.pop()

  def hoist_nested_functions(self):
    h = self.Hoister(self)
    h.hoist(self.ast_root)

    assert isinstance(self.ast_root, last.TopLevel)
    self.ast_root.body.entries = h.add_to_toplevel + self.ast_root.body.entries
    for tl in h.add_to_toplevel:
      tl.hidden = True
      self.insert_global_or_error(tl)

  def find_return_stmts(self, func):
    class FindReturns:
      def __init__(self): self.result = []
      def visit_Return(self, node): self.result.append(node)
    finder = FindReturns()
    self.visit(finder, func, do_not_cross_types=[last.FuncDef])
    return finder.result

  def expr_type(self, funcdef, expr):
    if expr is None:
      return _KEYWORDS['void']
    elif isinstance(expr, last.Number):
      return _KEYWORDS['i32']  # XXX all number types
    elif isinstance(expr, last.FuncCall):
      if isinstance(expr.func, last.Ident):
        f_in_globals = self.globals.get(expr.func.name)
        if isinstance(f_in_globals, last.FuncDef):
          if f_in_globals.rtype is _KEYWORDS['auto']:
            self.get_function_return_type(f_in_globals)
          return f_in_globals.rtype
    elif isinstance(expr, last.Ident):
      if fste := funcdef.symtab.get(expr.name):
        return fste.type
      assert False, "unhandled Ident expr_type %s" % expr
    elif isinstance(expr, last.Expr):
      if (expr.chain[1].name in ('+', '*', '-', '/') and
          self.expr_type(funcdef, expr.chain[0]) is _KEYWORDS['i32'] and
          self.expr_type(funcdef, expr.chain[2]) is _KEYWORDS['i32']):
        # HACK HACK HACK
        return _KEYWORDS['i32']
    assert False, "unhandled expr_type %s" % expr

  def get_function_return_type(self, fd):
    return_type = None
    returns = self.find_return_stmts(fd.body)
    for r in returns:
      this_type = self.expr_type(fd, r.value)
      if return_type is None:
        return_type = this_type
      elif return_type != this_type:
        self.error_at(r, 'returning "%s", previously "%s"' % (this_type, return_type))
    fd.rtype = return_type or _KEYWORDS['void']

  def determine_all_auto_function_returns(self):
    func_defs = self.find_func_defs(self.ast_root)
    for fd in func_defs:
      if fd.rtype is _KEYWORDS['auto']:
        self.get_function_return_type(fd)

  def infer_types(self):
    self.determine_all_auto_function_returns()

  def get_c_type(self, node):
    if node == _KEYWORDS['i32']:
      return 'int32_t'
    if node == _KEYWORDS['void']:
      return 'void'
    if node == _KEYWORDS['f32']:
      return 'float'
    if isinstance(node, last.PointerDecl):
      return self.get_c_type(node.base) + '*'
    if isinstance(node, last.Type):
      return node.base
    print('GET_C_TYPE', node)
    return '???'

  def get_safe_c_name(self, luv_name):
    # TODO
    return luv_name

  def expr(self, node):
    if isinstance(node, last.Ident):
      fste = self.current_function.symtab.get(node.name) if self.current_function else None
      if fste and fste.is_upval:
        return '*$up->%s' % self.get_safe_c_name(node.name)
      else:
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

      upvals = []
      if self.current_function:
        if isinstance(node.func, last.Ident):
          # TODO: this is obviously suck
          has_uv = self.current_function.upval_bindings.get(node.func.name)
          if has_uv:
            # TODO: double hacky, sneaky & here.
            upvals.append(last.Ident('&' + has_uv.parent_binding_name))

      result += ','.join(self.expr(x) for x in (upvals + node.args))
      result += ')'
      return result
    elif isinstance(node, last.Expr):
      result = ''
      for i,x in enumerate(node.chain):
        # Expr op Expr op Expr op ...
        if i % 2 == 0:
          result += '(%s)' % self.expr(x)
        else:
          # TODO: passing op right through
          result += x.name
      return result
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
        result += ' ' + self.expr(node.value)
      result += ';'
      return result
    elif isinstance(node, last.Pass):
      return ';'
    elif isinstance(node, last.Assign):
      return '%s = %s;' % (self.expr(node.lhs), self.expr(node.rhs))
    elif isinstance(node, last.VarDecl):
      if node.init:
        return '%s = %s;' % (self.get_safe_c_name(node.name), self.expr(node.init))
      else:
        return ''
    elif isinstance(node, last.FuncDef):
      return '/* HOISTED %s */;' % node.name
    else:
      return self.expr(node) + ';'

  def function_forward_declaration(self, func):
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
    # TODO: hidden are hoisted funcs, which should be static, but also need an
    # indication of exported/not at syntax level.
    is_static = 'static ' if func.hidden else ''
    return '%s%s %s(%s)' % (is_static, rtype, fname, params)

  def function_definition(self, func):
    result = self.function_forward_declaration(func)
    self.current_function = func
    result += '{'
    for n, fste in func.symtab.items():
      if fste.is_declared_local:
        if fste.type is _KEYWORDS['void']:
          self.error_at(fste.ref_node, 'can\'t declare local of type "%s"' % fste.type.base)
        result += '%(type)s %(name)s = (%(type)s){0};' % {
            'type': self.get_c_type(fste.type), 'name': self.get_safe_c_name(n)}
    for n, upval in func.upval_bindings.items():
      result += '%s %s = {' % (upval.struct_name, upval.parent_binding_name)
      for name, uv in upval.to_bind.items():
        in_cur_func = func.symtab[name]
        # If the source of this variable is already an upval (i.e. we're in the
        # "middle" function whose child references the variable, but it's
        # declared in our parent, then we need to pass it on from our upvals,
        # otherwise, refer to our local copy.
        if in_cur_func.is_upval:
          result += '$up->%s,' % name
        else:
          result += '&%s,' % name
      result += '};'
    result += self.stmt(func.body)
    result += '}'
    self.current_function = None
    return result

  def generate_upval_struct(self, obj):
    result = ''
    #pprint.pprint(obj)
    for n, uvb in obj.upval_bindings.items():
      result += 'typedef struct {'
      for name, uv in uvb.to_bind.items():
        result += '%s* %s;' % (self.get_c_type(uv.type), self.get_safe_c_name(name))
      result += '} %s;\n' % uvb.struct_name
    return result

  def compile(self, outfn):
    with open(outfn, 'w', newline='\n') as f:
      f.write(r'''#include <stdint.h>
#include <stdio.h>
static void printint(int x) {
  printf("%d\n", x);
}

/*
 * UPVAL STRUCTS
 */''')

      for n,obj in self.globals.items():
        if isinstance(obj, last.FuncDef):
          f.write(self.generate_upval_struct(obj))

      f.write(r'''
/*
 * FORWARD DECLARATIONS
 */''')
      for n,obj in self.globals.items():
        if isinstance(obj, last.FuncDef):
          f.write(self.function_forward_declaration(obj))
          f.write(';\n')

      f.write(r'''
/*
 * GLOBALS
 */''')
      for n,obj in self.globals.items():
        if isinstance(obj, last.VarDecl):
          if obj.type is _KEYWORDS['void']:
            self.error_at(obj, 'can\'t declare global of type "%s"' % obj.type.base)
          f.write('%(type)s %(name)s' % {
                'type': self.get_c_type(obj.type),
                'name': self.get_safe_c_name(obj.name)})
          if obj.init:
            f.write(' = %s' % self.expr(obj.init))
          f.write(';\n')

      f.write(r'''
/*
 * FUNCTIONS
 */''')
      for n,obj in self.globals.items():
        if isinstance(obj, last.FuncDef):
          f.write(self.function_definition(obj))

    subprocess.run(['clang-format', '-i', outfn, '-style=Chromium'])

def test_contents(fn):
  with open(fn, 'r') as f:
    source, _, after = f.read().partition('\n---\n')
  after = after.rstrip('\n')
  return source + '\n', after

def dyibicc(c_file):
  clang_path = 'clang'
  proc = subprocess.run([clang_path,
    '-c',
    '-fsyntax-only',
    '-Wall',
    '-Wextra',
    '-Werror',
    # Possibly detect these and error in our compile.
    '-Wno-unused-but-set-variable',
    '-Wno-unused-parameter',
    '-Wno-unused-variable',
    '-Wno-unused-function',
    c_file])
  if proc.returncode != 0:
    raise RuntimeError('clang compile failed')

  compiler_path = r'../dyibicc/out/wd/dyibicc.exe'
  proc = subprocess.run([compiler_path, c_file], capture_output=True, text=True)
  if proc.returncode != 0:
    print('---STDOUT', file=sys.stderr)
    print(proc.stdout, file=sys.stderr)
    print('---STDERR', file=sys.stderr)
    print(proc.stderr, file=sys.stderr)
    raise RuntimeError('compile failed')
  return proc.stdout.rstrip('\n')

def do_tests(parser, test_list, update):
  if not test_list:
    test_list = sorted(glob.glob('test/**/*.luv', recursive=True))

  disabled_list = []
  passed_list = []
  err = None
  def tt_error_at(node, msg):
    err['node'] = node
    err['msg'] = msg

  for t in test_list:
    #print(t)
    if '.disabled.' in t:
      disabled_list.append(t)
      continue
    t = t.replace('\\', '/')
    source, expected = test_contents(t)
    tree = parser.parse(source)
    #print(tree.pretty())
    ast = ToAst().transform(tree)
    #pprint.pprint(ast)
    if t.startswith('test/parse'):
      got = pprint.pformat(ast)
    elif t.startswith('test/type'):
      err = {}
      c = Compiler(t, ast, error_at=tt_error_at)
      c_file = os.path.splitext(t)[0] + '.c'
      c.compile(c_file)
      got = '!\n%s:%d:%d:%s' % (t, err['node'].line, err['node'].column, err['msg'])
    elif t.startswith('test/run'):
      c = Compiler(t, ast)
      c_file = os.path.splitext(t)[0] + '.c'
      #print(c_file)
      c.compile(c_file)
      got = dyibicc(c_file)

    if update:
      with open(t, "w", newline='\n') as f:
        f.write(source)
        f.write('---\n')
        f.write(got)
        f.write('\n')
    else:
      if expected != got:
        print()
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
    do_tests(parser, sys.argv[2:], update=False)
  elif len(sys.argv) >= 2 and sys.argv[1] == 'test_update':
    do_tests(parser, sys.argv[2:], update=True)
  else:
    source, _ = test_contents(sys.argv[1])
    tree = parser.parse(source + '\n')
    print(tree.pretty(), file=sys.stderr)

    ast = ToAst().transform(tree)
    import pprint
    pprint.pprint(ast, stream=sys.stderr)
    c = Compiler(sys.argv[1], ast)
    c_file = os.path.splitext(sys.argv[1])[0] + '.c'
    c.compile(c_file)
    dyibicc(c_file)

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
