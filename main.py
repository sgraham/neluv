import dataclasses
import glob
import inspect
import os
import pprint
import subprocess
import sys

from lark import Lark, Tree, Transformer, v_args, UnexpectedToken, logger, Visitor
from lark.indenter import PythonIndenter

import last

_KEYWORDS = {
  'auto': last.Type('auto'),
  'bool': last.Type('bool'),
  'f16': last.Type('f16'),
  'f32': last.Type('f32'),
  'f64': last.Type('f64'),
  'i16': last.Type('i16'),
  'i32': last.Type('i32'),
  'i64': last.Type('i64'),
  'i8': last.Type('i8'),
  'u16': last.Type('u16'),
  'u32': last.Type('u32'),
  'u64': last.Type('u64'),
  'u8': last.Type('u8'),
  'void': last.Type('void'),

  # This is a hack to forward decl memcpy, etc. that are semi-builtin and
  # require matching prototypes.
  'cvoid': last.Type('cvoid'),

  'float': last.Type('f32'),
  'double': last.Type('f64'),

  'false': last.Const('false'),
  'null': last.Const('null'),
  'true': last.Const('true'),

  'str': last.Type('str'),
}

_KEYWORDS['byte'] = _KEYWORDS['u8']
_KEYWORDS['double'] = _KEYWORDS['f64']
_KEYWORDS['float'] = _KEYWORDS['f32']
_KEYWORDS['int'] = _KEYWORDS['i32']

_IMPORTS_BY_FILENAME = {}

visit_tag_counter = 0
tmp_var_counter = 0
OP_MAP = {
    '+': '__add__',
    '-': '__sub__',
    '*': '__mul__',
    '/': '__div__',
    '%': '__mod__',

    '+=': '__iadd__',
    '-=': '__isub__',
    '*=': '__imul__',
    '/=': '__idiv__',
    '%=': '__imod__',

    # TODO: more
}

def get_tmp_var():
  global tmp_var_counter
  tmp_var_counter += 1
  return '$_%d' % tmp_var_counter

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

  def HEX_NUMBER(self, n):
    return int(n, 16)

  def OCT_NUMBER(self, n):
    return int(n, 8)

  def BIN_NUMBER(self, n):
    return int(n, 2)

  def FLOAT_NUMBER(self, n):
    return float(n)

  def NAME(self, n):
    #print('NAME', n, file=sys.stderr)
    return str(n)

  def BACKTICKED_LETTER(self, n):
    #print('NAME', n, file=sys.stderr)
    return str(n)

  def STRING(self, v):
    return v[1:-1]

  def FSTRING(self, v):
    return v[2:-1]

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

  def fstring(self, children):
    return last.Fstring(children[0])

  def ident(self, children):
    x = _KEYWORDS.get(children[0], None)
    if x:
      return x
    return last.Ident(children[0])

  def t_ident(self, children):
    return last.TIdent(children[0])

  def backticked_letter(self, children):
    return children[0]

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

  def exprlist(self, children):
    return children

  def testlist_tuple(self, children):
    return last.Tuple(children)

  def tuple(self, children):
    return last.Tuple(children)

  def getattr(self, children):
    return last.GetAttr(children[0], children[1])

  def cast(self, children):
    return last.Cast(children[0], children[1])

  def arith_expr(self, children):
    assert (len(children) - 3) % 2 == 0
    return last.Expr(children)

  def term(self, children):
    assert (len(children) - 3) % 2 == 0
    return last.Expr(children)

  def and_test(self, children):
    return last.And(children)

  def or_test(self, children):
    return last.Or(children)

  def not_test(self, children):
    assert len(children) == 1
    return last.Not(children[0])

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

  def list_decl(self, children):
    return last.ListDecl(children[0])

  def fixed_array_decl(self, children):
    return last.FixedArrayDecl(size=children[0], base=children[1])

  def pointer_decl(self, children):
    return last.PointerDecl(children[0])

  def optional_decl(self, children):
    return last.OptionalDecl(children[0])

  def tuple_decl(self, children):
    return last.TupleDecl(children)

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

  def import_stmt(self, children):
    return children[0]

  def import_from(self, children):
    if not isinstance(children[0], last.ImportPackage):
      c0 = last.ImportPackage(children[0], None)
    if len(children) == 1:
      return last.ImportFrom(c0, None)
    else:
      return last.ImportFrom(c0, children[1])

  def import_name(self, children):
    return last.Import(children[0], None)

  def import_as_names(self, children):
    return children

  def import_as_name(self, children):
    return last.ImportItem(children[0], children[1])

  def dotted_as_names(self, children):
    return children[0]

  def dotted_as_name(self, children):
    return last.ImportPackage(children[0], children[1])

  def dotted_name(self, children):
    return children

  def continue_stmt(self, children):
    return last.Continue()

  def break_stmt(self, children):
    return last.Break()

  def return_stmt(self, children):
    return last.Return(children[0])

  def del_stmt(self, children):
    return last.Del(children)

  def pass_stmt(self, children):
    return last.Pass()

  def external_stmt(self, children):
    return last.External()

  def assert_stmt(self, children):
    return last.Assert(children[0], children[1])

  def nonlocal_stmt(self, children):
    return last.Nonlocal(children)

  def for_stmt(self, children):
    return last.For(children[0], children[1], children[2], children[3])

  def while_stmt(self, children):
    return last.While(children[0], children[1], children[2])

  def if_stmt(self, children):
    return last.If(children[0], children[1], children[2], children[3])

  def elif_(self, children):
    return last.Elif(children[0], children[1])

  def elifs(self, children):
    return children

  def optional_unwrap(self, children):
    return last.OptionalUnwrap(children[0], children[1])

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

  def augassign(self, children):
    return last.AugAssign(children[0], children[1], children[2])

  def augassign_op(self, children):
    return children[0]

  def list(self, children):
    return last.List(children)

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

  def methoddef(self, children):
    #print('METHODDEF', children)
    struct = children[0]
    assert isinstance(struct, last.Ident) or isinstance(struct, last.TIdent)
    rtype = children[1] or _KEYWORDS['auto']
    funcname = children[2]
    selfname = children[3]
    args = children[4] or []
    body = children[5]
    args_with_self = [last.TypedVar(last.PointerDecl(struct), selfname)] + args
    if isinstance(struct, last.Ident):
      joined = last.Ident(struct.name + '$' + funcname)
    else:
      joined = last.JoinIdents([struct, last.Ident('$' + funcname)])
    #print('METHODDEF', joined)
    return last.FuncDef(rtype, joined, args_with_self, body)

  def import_macros_stmt(self, children):
    return last.ImportMacros(children[0])

  def quote_stmt(self, children):
    return last.Quote(children[0], children[1])

  def funcdecl(self, children):
    type = children[0] or _KEYWORDS['auto']
    params = children[1]
    return last.FuncType(base=None, rtype=type, params=params)

  def comprehension(self, children):
    if len(children) == 2:
      return last.Comprehension(children[0], children[1], None)
    elif len(children) == 3:
      return last.Comprehension(children[0], children[1], children[2])
    assert False

  def list_comprehension(self, children):
    return last.ListComprehension(children[0])

  def comp_fors(self, children):
    return children

  def comp_for(self, children):
    return last.ComprehensionFor(children[0], children[1])

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

  def expr_stmt(self, children): return children[0]
  def assign_stmt(self, children): return children[0]

  def start(self, children):
    return last.TopLevel(last.Block(children))

class Parser:
  def __init__(self, prelude):
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

    self.prelude = prelude

  def parse(self, code, include_prelude=True):
    try:
      before = self.prelude if include_prelude else ''
      return self.parser.parse(before + code)
    except UnexpectedToken as err:
      return Tree('error', children=[last.ParseError(err.line, err.column, err.token)])

class Typer:
  def __init__(self):
    pass

class GeneratedStructInfo:
  def __init__(self, node, struct):
    self.node = node
    self.struct = struct

class Compiler:
  def __init__(self, filename, ast_root, parser, error_callback=None):
    self.globals = {}  # values are SymTabEntry
    self.filename = filename

    def default_error_at(node, msg):
      print('%s:%d:%d:error: %s' % (self.filename, node.line, node.column, msg), file=sys.stderr)
      sys.exit(1)

    def flag_error_and_tell_user(node, msg):
      self.have_error = True
      self.error_callback(node, msg)

    self.have_error = False
    self.error_callback = error_callback or default_error_at
    self.error_at = flag_error_and_tell_user

    self.generated_structs = {}

    self.ast_root = ast_root
    self.parser = parser

    self.current_function = None
    self.current_function_saved = []

    self.find_globals()
    self.resolve_type_names()
    self.build_function_symtabs()
    self.hoist_nested_functions()
    self.resolve_idents()
    self.infer_types()

    for contained, gsi in self.generated_structs.items():
      assert isinstance(gsi.struct.name, last.Ident)
      self.globals[gsi.struct.name.name] = last.SymTabEntry(gsi.node, gsi.struct)

  def is_lexically_before(self, a, b):
    if a.line == b.line: return a.column < b.column
    return a.line < b.line

  class FuncSymTab:
    def __init__(self, func, parent):
      self.func = func
      self.parent = parent
      for p in func.params:
        assert isinstance(p, last.TypedVar)
        func.add_to_symtab(p.name, last.SymTabEntry(p.type, p, is_func_param=True))

    def visit_VarDecl(self, node):
      x = self.func.find_in_symtab(node.name)
      if x:
        if x.is_pending_nonlocal and self.parent.is_lexically_before(node, x.ref_node):
          self.parent.error_at(node, 'name "%s" is used before nonlocal declaration' % node.name)
        else:
          assert isinstance(self.func.name, last.Ident)
          self.parent.error_at(node,
              'redefinition of "%s" in "%s"' % (node.name, self.func.name.name))
        return

      # TODO: This is probably in the wrong place. resolve_type_names makes more
      # sense, but has no symtabs yet.
      if isinstance(node.type, last.Ident):
        ste = self.func.find_in_symtab(node.type.name)
        if not ste:
          ste = self.parent.globals.get(node.type.name)
        if not ste:
          self.error_at(node, "%s undefined" % node.type.name)
        # TODO: Type vs Struct
        assert isinstance(ste.ref_node, last.Struct)
        node.type = last.Type(ste.ref_node)

      self.func.add_to_symtab(node.name,
                              last.SymTabEntry(node.type, node, is_declared_local=True))

    def visit_For(self, node):
      if isinstance(node.it, list):
        for x in node.it:
          self.local(x)
      else:
        assert isinstance(node.it, last.Ident)
        self.local(node.it)

    def local(self, ident):
      x = self.func.find_in_symtab(ident.name)
      if not x:
        self.func.add_to_symtab(ident.name, last.SymTabEntry(
          _KEYWORDS['auto'], ident, is_declared_local=True))
      elif x.is_pending_nonlocal and self.parent.is_lexically_before(ident, x.ref_node):
        self.parent.error_at(ident, 'name "%s" is used before nonlocal declaration' % ident.name)

    def visit_OptionalUnwrap(self, unwrap):
      # TODO: This is sort of python-y but not good either. The bind target is
      # function scope like all locals, but that doesn't really make sense for
      # an if block style unwrap.
      self.local(unwrap.bind)

    def visit_Assign(self, node):
      if isinstance(node.lhs, last.Ident):
        self.local(node.lhs)
      elif isinstance(node.lhs, last.Tuple):
        if all(isinstance(x, last.Ident) for x in node.lhs.items):
          for x in node.lhs.items:
            self.local(x)

    def visit_TupleDecl(self, tup):
      #print('TUPLE_DECL', tup)
      #field_types = [self.parent.expr_type(self.func, v) for v in tup.base]
      #self.parent.create_tuple_struct(field_types, tup)
      pass


  class ScanForNonlocal:
    def __init__(self, func, parent):
      self.func = func
      self.parent = parent
    def visit_Nonlocal(self, node):
      for name in node.vars:
        self.func.add_to_symtab(name, last.SymTabEntry(None, node, is_pending_nonlocal=True))

  def build_function_symtab(self, f):
    f.push_empty_symtab_scope()
    self.Visit(self.ScanForNonlocal(f, self), f.body, do_not_cross_types=[last.FuncDef])
    self.Visit(self.FuncSymTab(f, self), f.body, do_not_cross_types=[last.FuncDef])

  def build_function_symtabs(self):
    for f in self.find_func_defs(self.ast_root):
      self.build_function_symtab(f)

  class Visit:
    def __init__(self, visitor, node, do_not_cross_types=None):
      self.visitor = visitor
      self.start = node
      self.do_not_cross_types = do_not_cross_types
      self.visited = set()
      global visit_tag_counter
      visit_tag_counter += 1
      self.visit_tag = visit_tag_counter
      self.impl(self.start)

    def impl(self, node):
      to_return = None

      if hasattr(node, 'tag_for_visit') and getattr(node, 'tag_for_visit') == self.visit_tag:
        return

      x = getattr(self.visitor, 'visit_' + node.__class__.__name__, None)
      if x:
        result = x(node)
        if result is not None:
          to_return = result

      if to_return:
        to_return.tag_for_visit = self.visit_tag
      else:
        node.tag_for_visit = self.visit_tag

      if self.do_not_cross_types:
        for dnct in self.do_not_cross_types:
          if isinstance(node, dnct):
            # XXX ugly copy pasta to keep in sync below
            x = getattr(self.visitor, 'after_' + node.__class__.__name__, None)
            if x:
              after_to_return = x(node)
              if after_to_return:
                assert not to_return, 'both initial visit_ and after_ tried to replace'
                to_return = after_to_return
            return to_return

      for f in dataclasses.fields(node):
        field = getattr(node, f.name)

        if isinstance(field, last.AstNode) or isinstance(field, last.Type):
          ret = self.impl(field)
          if ret is not None:
            setattr(node, f.name, ret)
        elif isinstance(field, list):
          for i, lx in enumerate(field):
            if isinstance(lx, last.AstNode) or isinstance(lx, last.Type):
              ret = self.impl(lx)
              if ret is not None:
                field[i] = ret

      # XXX ugly copy pasta to keep in sync above
      x = getattr(self.visitor, 'after_' + node.__class__.__name__, None)
      if x:
        after_to_return = x(node)
        if after_to_return:
          assert not to_return, 'both initial visit_ and after_ tried to replace'
          to_return = after_to_return
      return to_return

  def insert_global_or_error(self, name, node):
    if self.globals.get(name):
      self.error_at(node, 'redefinition at global scope of "%s"' % name)
    ty = None
    if isinstance(node, last.VarDecl):
      ty = node.type
    self.globals[name] = last.SymTabEntry(ty, node, is_global=True)

  def find_and_read_file_to_load(self, fn):
    fn_to_open = fn
    if not os.path.isfile(fn_to_open):
      fn_to_open = os.path.join(os.path.split(self.filename)[0], fn)
    with open(fn_to_open, 'r') as f:
      return f.read()

  def load_macros(self, fn):
    source = self.find_and_read_file_to_load(fn)
    glob = {}
    loc = {}
    exec(source, glob, loc)
    for name,func in loc.items():
      if inspect.isfunction(func):
        co_mem = inspect.getmembers(func.__code__)
        for n,v in co_mem:
          if n == 'co_argcount' and v == 1:
            for l,o in loc.items():
              func.__globals__[l] = o
            self.insert_global_or_error(name, last.MacroDef(name, func))
            break

  def load_package(self, imp_pkg):
    # TODO: some sort of canonicalization probably
    assert len(imp_pkg.what) == 1, "todo; affect global names inserted by insert_global_or_error"
    fn = '.'.join(imp_pkg.what) + '.luv'
    if x := _IMPORTS_BY_FILENAME.get(fn):
      return x
    source = self.find_and_read_file_to_load(fn)
    tree = self.parser.parse(source + '\n', include_prelude=False)
    ast = ToAst().transform(tree)
    sub_compiler = Compiler(fn, ast, self.parser, self.error_callback)
    pkg = last.Package(imp_pkg.what[0], sub_compiler.globals)
    _IMPORTS_BY_FILENAME[fn] = pkg
    return pkg

  def find_globals(self):
    assert isinstance(self.ast_root, last.TopLevel), self.ast_root

    add_to_toplevel = []
    for tl in self.ast_root.body.entries:
      if (isinstance(tl, last.FuncDef) or
          isinstance(tl, last.Struct)):
        assert isinstance(tl.name, last.Ident), str(tl.name)
        self.insert_global_or_error(tl.name.name, tl)
      elif isinstance(tl, last.VarDecl):
        self.insert_global_or_error(tl.name, tl)
      elif isinstance(tl, last.Assign) and isinstance(tl.lhs, last.Ident):
        # Handled below.
        pass
      elif isinstance(tl, last.ImportMacros):
        self.load_macros(tl.filename.value)
      elif isinstance(tl, last.On):
        for f in tl.block.entries:
          if not isinstance(f, last.FuncDef):
            self.error_at(f, 'expecting only function definitions in "on" block')
          f.name = '%s$%s' % (tl.name, f.name)
          self.insert_global_or_error(f.name, f)
      elif isinstance(tl, last.Quote):
        self.insert_global_or_error(tl.name, tl)
      elif isinstance(tl, last.Import):
        package = self.load_package(tl.package)
        self.insert_global_or_error(package.name, package)
      elif isinstance(tl, last.ImportFrom):
        package = self.load_package(tl.package)
        # TODO: this only supports function import currently
        for ii in tl.items:
          if x := package.globals.get(ii.what):
            func = x.ref_node
            if ii.renamed:
              copy = func.clone()
              copy.name = last.Ident(ii.renamed)
              args = [last.Ident(p.name) for p in func.params]
              internal_name = last.Ident(ii.what)
              internal_name.special = True
              copy.body = last.Block([last.Return(last.FuncCall(internal_name, args))])
              copy.hidden = True
              add_to_toplevel.append(copy)
              assert isinstance(copy.name, last.Ident)
              self.insert_global_or_error(copy.name.name, copy)
            else:
              assert isinstance(func.name, last.Ident)
              self.insert_global_or_error(func.name.name, func)
          else:
            self.error_at(ii, '%s not found in %s' % (ii.what, package.name))
      else:
        #pprint.pprint(tl)
        self.error_at(tl, 'unexpected at top level %s' % tl)

    self.ast_root.body.entries.extend(add_to_toplevel)

    for i, tl in enumerate(self.ast_root.body.entries):
      if isinstance(tl, last.Assign) and isinstance(tl.lhs, last.Ident):
        # Turn simple Assign into VarDecl at global scope
        x = last.VarDecl(self.expr_type(None, tl.rhs), tl.lhs.name, tl.rhs)
        x.copy_meta(tl)
        self.ast_root.body.entries[i] = x
        self.insert_global_or_error(x.name, x)
      # TODO: multiple return tuple assignments

  def resolve_type_names(self):
    # Resolve idents in structs to point at other structs (TODO: should this be here?)
    # XXX this is ugly
    # XXX doesn't handle nested types either
    # XXX probably needs to be elsewhere so that function auto return are
    # already resolved too
    for n,ste in self.globals.items():
      obj = ste.ref_node
      if isinstance(obj, last.Struct):
        for f in obj.members:
          if isinstance(f.type, last.Ident):
            resolved = self.globals.get(f.type.name)
            if resolved.ref_node and isinstance(resolved.ref_node, last.Struct):
              f.type = resolved.ref_node.cached_type()
          elif isinstance(f.type, last.PointerDecl):
            t = f.type
            prev = None
            while isinstance(t, last.PointerDecl):
              prev = t
              t = t.base
            if isinstance(t, last.Ident):
              resolved = self.globals.get(t.name)
              if resolved.ref_node and isinstance(resolved.ref_node, last.Struct):
                # TODO: rationalize why are some Type and this one directly Struct
                prev.base = resolved.ref_node
      if isinstance(obj, last.FuncDef):
        if isinstance(obj.rtype, last.Ident):
          resolved = self.globals.get(obj.rtype.name)
          if resolved.ref_node and isinstance(resolved.ref_node, last.Struct):
            obj.rtype = resolved.ref_node.cached_type()
        for p in obj.params:
          assert isinstance(p, last.TypedVar)
          if isinstance(p.type, last.Ident):
            resolved = self.globals.get(p.type.name)
            if resolved.ref_node and isinstance(resolved.ref_node, last.Struct):
              # TODO: Type vs. Struct sucks
              p.type = last.Type(resolved.ref_node.cached_type())
          elif isinstance(p.type, last.PointerDecl):
            t = p.type
            prev = None
            while isinstance(t, last.PointerDecl):
              prev = t
              t = t.base
            if isinstance(t, last.Ident):
              resolved = self.globals.get(t.name)
              if resolved.ref_node and isinstance(resolved.ref_node, last.Struct):
                # TODO: rationalize why are some Type and this one directly Struct
                prev.base = resolved.ref_node



  def find_func_defs(self, start, top_level_only=False):
    class FindFuncDef:
      def __init__(self): self.result = []
      def visit_FuncDef(self, node): self.result.append(node)
    finder = FindFuncDef()
    no_cross = [last.FuncDef] if top_level_only else []
    no_cross.append(last.Quote)
    self.Visit(finder, start, do_not_cross_types=no_cross)
    return finder.result

  def replace_ident_references(self, start, old, new):
    class ReplaceIdents:
      def visit_Ident(self, v):
        if v.name == old:
          v.name = new
    self.Visit(ReplaceIdents(), start)

  def find_upvals(self, func, lexical_func_stack):
    class FindIdents:
      def __init__(self): self.idents = []
      def visit_Ident(self, v): self.idents.append(v.name)
      def visit_Nonlocal(self, v): self.idents.extend(v.vars)
    finder = FindIdents()
    # We do have to decend into sub-functions here (i.e. not just the strict
    # body of this function) because if a further nested function refers to
    # something above this function, we need to request it from the parent.
    self.Visit(finder, func.body)

    # Find all the identifiers referenced in this function that refer to a
    # parent scope. Add entries to this function's symtab (marking them as
    # upval) and also return them.
    to_bind = {}
    for i in finder.idents:
      pending_non_local = None
      pending_non_local_name = None
      for f in reversed(lexical_func_stack):
        in_upper = f.find_in_symtab(i)
        if in_upper and in_upper.is_pending_nonlocal:
          # If it was found, but it's marked as nonlocal, then we need to search
          # higher, so note that we are searching for it and continue (so that
          # we can fail out if it's not found at a higher scope).
          pending_non_local = in_upper
          pending_non_local_name = i
          continue
        if in_upper:
          if f != func:
            #print('upval req for %s of %s, found in %s' % (i, func.name, f.name))
            ste = last.SymTabEntry(
                in_upper.type, in_upper.ref_node, is_upval=True, func_ref_if_upval=f)
            if pending_non_local:
              func.replace_in_symtab(i, ste)
            else:
              func.add_to_symtab(i, ste)
            to_bind[i] = ste
            pending_non_local = pending_non_local_name = None
            break
          else:
            break
      else:
        if pending_non_local:
          if x := self.globals.get(i):
            # If it's a global, then we can just reference it, no need to pass
            # it in from the parent, but don't error out.
            pending_non_local.is_global = True
            pending_non_local.type = x.type
          else:
            self.error_at(pending_non_local.ref_node,
                'no binding for nonlocal "%s" found' % pending_non_local_name)

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
          assert isinstance(nested.name, last.Ident)
          assert isinstance(cur.name, last.Ident)
          old_name = nested.name.name
          new_name = old_name + '$%s' % cur.name.name
          nested.name = last.Ident(new_name)

          to_bind = self.parent.find_upvals(nested, self.cur_func_stack + [nested])
          if to_bind:
            uvb = last.UpvalBindings(to_bind, new_name)
            cur.upval_bindings[new_name] = uvb
            nested.params.insert(0,
                last.TypedVar(last.PointerDecl(uvb.struct), '$up'))

          # Remove the declaration from the body of the current function,
          # replacing calls to it.
          cur.body.entries.remove(nested)  # TODO: prob unnecessary O(n)
          cur.nested_funcs_to_push_upvals.append(nested)
          self.add_to_toplevel.append(nested)
          # TODO: this is probably wrong/too simple; at least need to have
          # something to deal with a local declared with the same name as a
          # function.
          self.parent.replace_ident_references(cur.body, old_name, new_name)
          cur.add_to_symtab(new_name, last.SymTabEntry(
              _KEYWORDS['auto'], nested, is_declared_local=True, is_hoisted_function=True))
          #pprint.pprint(cur_func)

        self.cur_func_stack.append(nested)
        self.hoist(nested.body)
        self.cur_func_stack.pop()

  def hoist_nested_functions(self):
    h = self.Hoister(self)
    h.hoist(self.ast_root)

    assert isinstance(self.ast_root, last.TopLevel)
    # TODO: test/run/nested_func_ref_up_double.luv (e.g.) depends on the hoisted
    # functions being appended rather than prepended because a later walk to
    # resolve upvals relies on the outer function types being resolved before
    # walking the nested functions which allows upval types to be found. This is
    # pretty fragile.
    self.ast_root.body.entries = self.ast_root.body.entries + h.add_to_toplevel
    for tl in h.add_to_toplevel:
      tl.hidden = True
      assert isinstance(tl.name, last.Ident)
      self.insert_global_or_error(tl.name.name, tl)

  # TODO: this could go in prelude too
  def create_tuple_struct(self, field_types, node):
    #print('CREATE_TUPLE_STRUCT', node, field_types)
    c_name_field_types = [self.get_mangled_c_type(t) for t in field_types]
    members = [last.TypedVar(t, '_%d' % i) for i,t in enumerate(field_types)]
    name = '$Tuple$' + '$'.join(str(x) for x in c_name_field_types)
    if name in self.generated_structs:
      return
    struct = last.Struct(last.Ident(name), members)
    struct.omit_constructor = True
    self.generated_structs[name] = GeneratedStructInfo(node, struct)

  def get_list_struct_for_contained_type(self, elem_type):
    base_type_name = self.get_mangled_c_type(elem_type)
    # This should have been created ResolveIdents.make_list_struct (if it fails here).
    return self.generated_structs[base_type_name].struct

  def create_list_struct(self, elem_type, node):
    result = self.expand_macro(
        last.FuncCall(last.Ident('List'), [elem_type]), self.globals.get('List').ref_node)
    base_type_name = self.get_mangled_c_type(elem_type)
    struct = self.globals[result.func.name].ref_node
    # TODO XXX: Opt and List conflict by base_type_name here (very dumb)
    self.generated_structs[base_type_name] = GeneratedStructInfo(node, struct)
    return struct

  class ResolveIdents:
    def __init__(self, parent):
      self.parent = parent
      assert self.parent.current_function is None

    def visit_FuncDef(self, func):
      assert not self.parent.current_function
      self.parent.current_function = func

    def resolve_ident(self, ident, rhs_type, tuple_index):
      if tuple_index is not None:
        if isinstance(rhs_type, last.Type) and isinstance(rhs_type.base, last.Struct):
          rhs_type = rhs_type.base
          rhs_type = rhs_type.members[tuple_index].type
        elif isinstance(rhs_type, last.TupleDecl):
          rhs_type = rhs_type.base[tuple_index]
        else:
          assert False, "todo; tuple style?"
      x = self.parent.current_function.find_in_symtab(ident.name)
      assert x, "ident not in scope? '%s'" % ident.name
      if x.type is _KEYWORDS['auto']:
        x.type = rhs_type
        self.push_into_upvars(ident, x)
      else:
        if x.type != rhs_type:
          if (isinstance(x.type, last.OptionalDecl) and
              (x.type.base is rhs_type or rhs_type is _KEYWORDS['null'])):
            # Allow coercion from contained type of optional to the optional,
            # or from null to any optional.
            pass
          else:
            self.parent.error_at(
                ident, 'previously typed as "%s", now "%s"' % (x.type, rhs_type))

    def visit_For(self, node):
      if isinstance(node.it, last.Ident):
        tuple_index = 0

      coll_type = self.parent.expr_type(self.parent.current_function, node.collection)
      if it_type := self.parent.result_type_of_method(coll_type, '__iter__', errnode=node):
        it_return_type = self.parent.result_type_of_method(it_type, '__next__', errnode=node)
        assert (isinstance(it_return_type, last.Type) and
                isinstance(it_return_type.base, last.Struct))
        assert it_return_type.base.members[1].name == '_1'
        rhs_type = it_return_type.base.members[1].type
      else:
        assert False, "todo %s" % coll_type
      self.resolve_ident(node.it, rhs_type, tuple_index=None)

    def after_Assign(self, assign):
      if isinstance(assign.lhs, last.Ident):
        rhs_type = self.parent.expr_type(self.parent.current_function, assign.rhs)
        self.resolve_ident(assign.lhs, rhs_type, tuple_index=None)
      elif isinstance(assign.lhs, last.Tuple):
        assert all(isinstance(x, last.Ident) for x in assign.lhs.items)
        rhs_type = self.parent.expr_type(self.parent.current_function, assign.rhs)
        for i,x in enumerate(assign.lhs.items):
          self.resolve_ident(x, rhs_type, tuple_index=i)

    def visit_OptionalDecl(self, od):
      c_base_type_name = self.parent.get_mangled_c_type(od.base)
      if c_base_type_name not in self.parent.generated_structs:
        opt_struct_name = '$Opt$' + c_base_type_name
        members = [last.TypedVar(_KEYWORDS['bool'], 'has'),
                   last.TypedVar(od.base, 'val')]
        struct = last.Struct(last.Ident(opt_struct_name), members)
        struct.omit_constructor = True
        self.parent.generated_structs[c_base_type_name] = GeneratedStructInfo(od, struct)

    def visit_OptionalUnwrap(self, ou):
      assert isinstance(ou.bind, last.Ident)
      opt_type = self.parent.expr_type(self.parent.current_function, ou.optexpr)
      assert isinstance(opt_type, last.OptionalDecl)
      self.resolve_ident(ou.bind, opt_type.base, tuple_index=None)

    def visit_ListComprehension(self, lc):
      elem_type = self.parent.expr_type(self.parent.current_function, lc.body.result)
      self.parent.create_list_struct(elem_type, lc)

    def visit_List(self, l):
      if len(l.values) == 0:
        self.parent.error_at(l, "can't determine type of empty list yet")
      t = self.parent.expr_type(self.parent.current_function, l.values[0])
      for i in l.values[1:]:
        t2 = self.parent.expr_type(self.parent.current_function, i)
        if t is not t2:
          self.error_at(l, 'inconsistent types in list, was "%s" now "%s"' % (t, t2))
      self.parent.create_list_struct(t, l)

    def visit_FuncCall(self, funccall):
      if isinstance(funccall.func, last.Ident):
        glob = self.parent.globals.get(funccall.func.name)
        if glob and isinstance(glob.ref_node, last.MacroDef):
          return self.parent.expand_macro(funccall, glob.ref_node)

    # In nested_func_ref_up, the attempt to expand print(stuff()) previously
    # failed because the type of the up value |x| in stuff() hasn't been
    # resolved. That resolution was happening in after_FuncDef (once main() was
    # fully traversed), but that means that the macro in the body of main()
    # can't ask for the return type of stuff() because the upval that stuff()
    # returns is not yet typed. Instead, push_into_upvars() pushes the reference
    # into the nested function immediately when traversing main().
    # TBD whether calling stuff() before `def stuff()` should be valid. It
    # wouldn't be in Python for a different reason.
    #
    # Secondarily, in nested_func_ref_up_double, the |y| in things() previously
    # was not resolved because we were only pushing into the upvals structure
    # for the current function. To fix |y|, when hoisting nested functions we
    # have to keep track of a list of the nested functions and then push into
    # all of their upval structures too (FuncDef.nested_funcs_to_push_upvals)
    #
    # TODO:
    # Thirdly, nested_func_ref_up_double_mixed.luv tries to resolve the type of
    # stuff(), which requires the return type of its nested function things().
    # Determining the return value of stuff() currently only walks the body
    # looking for returns and tries to type those. However, in order to type
    # things(), it needs to first walk the rest of the body of stuff() so that
    # |z| will be resolved and pushed as an upvar into things(). So some
    # reordering is required here. Since macro calls are during
    # resolve_idents(), resolve_function_return_type() should probably be a full
    # walk of the items of the function, rather than skimming through to get
    # only return statements. Maybe just a resolve_idents() of the stuff()
    # first? And we probably need a tag on ast nodes to say they're resolved to
    # avoid redoing things over and over.

    def push_into_upvars(self, ident, x):
      def push_into(func):
        for nested_name, uvb in func.upval_bindings.items():
          # Resolving references to upvals that were previously untyped
          # (|x| in test/run/nested_func_ref_up.luv)
          ste = uvb.to_bind.get(ident.name)
          if ste:
            assert ste.is_upval and ste.func_ref_if_upval
            if ste.type is _KEYWORDS['auto']:
              ste.type = ste.func_ref_if_upval.find_in_symtab(ident.name).type

              # And also the members of the upval structure
              # (|y| in test/run/nested_func_ref_up_double.luv).
              for mem in uvb.struct.members:
                if mem.name == ident.name:
                  mem.type = ste.type

        for f in func.nested_funcs_to_push_upvals:
          push_into(f)

      push_into(self.parent.current_function)

    def after_FuncDef(self, func):
      assert self.parent.current_function == func
      self.parent.current_function = None

    def visit_TupleDecl(self, tup):
      #print('TUPLE_DECL RESOLVE', tup)
      field_types = [self.parent.expr_type(self.parent.current_function, v) for v in tup.base]
      self.parent.create_tuple_struct(field_types, tup)

  def resolve_idents(self, start_at=None):
    if start_at:
      self.current_function_saved.append(self.current_function)
      self.current_function = None

    resolver = self.ResolveIdents(self)
    self.Visit(resolver, self.ast_root if not start_at else start_at,
               do_not_cross_types=[last.Quote])

    if start_at:
      self.current_function = self.current_function_saved.pop()

  def expand_macro(self, node, mac):
    assert (isinstance(node, last.FuncCall) and isinstance(node.func, last.Ident)
            and isinstance(mac, last.MacroDef)), \
                str(node) + '\n---\n' + str(node.func) + '\n---\n' + str(mac)
    #print("CALLING MACRO", node.func.name)

    class Quotes:
      def __init__(self, globs):
        for n,data in globs.items():
          if isinstance(data.ref_node, last.Quote):
            setattr(self, n, data.ref_node)

    class Unquoter:
      def __init__(s, subs):
        s.subs = subs

      def visit_TIdent(s, ti):
        #print('TRYING TO SUB', ti.name)
        subwith = s.subs.get(ti.name)
        if not subwith:
          s.error_at(ti, 'trying to unquote "%s", but not provided' % ti.name)
        return subwith

      def after_JoinIdents(s, ji):
        assert all(isinstance(x, last.Ident) for x in ji.idents), str(ji)
        return last.Ident(''.join(x.name for x in ji.idents))

    class Macro:
      def __init__(s):
        s.args = node.args
        s.block = None
        s.func = self.current_function
        s.keywords = _KEYWORDS
        s.quotes = Quotes(self.globals)
      def expr_type(s, node):
        ret = self.expr_type(self.current_function, node)
        if ret is _KEYWORDS['auto']:
          assert False, 'internal error, unable to get type for "%s"' % node
        return ret
      def get_c_type(s, ty):
        return self.get_mangled_c_type(ty)
      def keyword_or_ident(s, name):
        x = _KEYWORDS.get(name, None)
        if x:
          return x
        return last.Ident(name)
      def parse_expr(s, code):
        tree = self.parser.parse(code + '\n', include_prelude=False)
        ast = ToAst().transform(tree)
        return ast.body.entries[0]
      def parse_toplevel(s, code):
        tree = self.parser.parse(code + '\n', include_prelude=False)
        ast = ToAst().transform(tree)
        return ast
      def have_global(s, glob):
        return glob in self.globals
      def insert_global(s, name, glob):
        self.insert_global_or_error(name, glob)
        self.ast_root.body.entries.append(glob)
        if isinstance(glob, last.FuncDef):
          self.build_function_symtab(glob)
          # XXX XXX XXX I think this needs to do the resolve_types
          self.resolve_idents(glob)
        #pprint.pprint(glob)
      def unquote(s, ast, subs):
        unquoter = Unquoter(subs)
        self.Visit(unquoter, ast)
        return ast
    macro = Macro()
    result = mac.pyfunc(macro)
    self.resolve_type_names()
    self.resolve_idents(result)
    return result

  def find_return_stmts(self, func):
    class FindReturns:
      def __init__(self): self.result = []
      def visit_Return(self, node): self.result.append(node)
    finder = FindReturns()
    self.Visit(finder, func, do_not_cross_types=[last.FuncDef])
    return finder.result

  def tuple_struct_for_types(self, field_types):
    c_name_field_types = [self.get_mangled_c_type(t) for t in field_types]
    name = '$Tuple$' + '$'.join(str(x) for x in c_name_field_types)
    self.create_tuple_struct(field_types, None)
    return self.generated_structs[name].struct

  def tuple_struct_for_values(self, func, values):
    field_types = [self.expr_type(func, v) for v in values]
    return self.tuple_struct_for_types(field_types)

  def method_name(self, static_type, method_name):
    # XXX Type vs Struct
    if isinstance(static_type, last.Type):
      return '%s$%s' % (static_type.base.name.name, method_name)
    elif isinstance(static_type, last.Struct):
      return '%s$%s' % (static_type.name.name, method_name)
    else:
      assert False, "type or struct"

  def result_type_of_method(self, static_type, method_name, errnode):
    # XXX Type vs Struct
    if isinstance(static_type, last.Type) and isinstance(static_type.base, last.Struct):
      ty = static_type.base
    elif isinstance(static_type, last.Struct):
      ty = static_type

    func_name = self.method_name(ty, method_name)
    ste_in_globals = self.globals.get(func_name)
    if ste_in_globals:
      in_globals = ste_in_globals.ref_node
      if not self.resolve_function_return_type(in_globals):
        return None  # TODO: test for this case, can it get hit?
      return in_globals.rtype
    else:
      self.error_at(errnode, 'no %s found on "%s"' % (method_name, ty.name))

  def expr_type(self, funcdef, expr):
    if expr is None:
      return _KEYWORDS['void']
    elif isinstance(expr, last.Number):
      return _KEYWORDS['i32']  # XXX all number types
    elif isinstance(expr, last.Const) and expr.name == 'true':
      return _KEYWORDS['bool']
    elif isinstance(expr, last.Const) and expr.name == 'false':
      return _KEYWORDS['bool']
    elif isinstance(expr, last.Const) and expr.name == 'null':
      # Type of null is itself? Not sure.
      return _KEYWORDS['null']
    elif isinstance(expr, last.String):
      return _KEYWORDS['str']
    elif isinstance(expr, last.Fstring):
      return _KEYWORDS['str']
    elif isinstance(expr, last.Package):
      return expr
    elif isinstance(expr, last.FuncCall):
      if isinstance(expr.func, last.Ident):
        if expr.func.name == 'iter':
          assert len(expr.args) == 1
          arg_type = self.expr_type(funcdef, expr.args[0])
          return self.result_type_of_method(arg_type, '__iter__', errnode=expr)

        if expr.func.name == 'sizeof':
          assert len(expr.args) == 1
          return _KEYWORDS['int']   # TODO: 32/64

        if expr.func.name == 'unreachable':
          assert len(expr.args) == 0
          return _KEYWORDS['void']

        if expr.func.name == 'hash':
          assert len(expr.args) == 1
          return _KEYWORDS['u64']

        if expr.func.name == 'zeroed':
          assert len(expr.args) == 1
          return self.expr_type(funcdef, expr.args[0])

        if expr.func.name == 'next':
          assert len(expr.args) == 1
          arg_type = self.expr_type(funcdef, expr.args[0])
          #print('NEXT', arg_type)
          if isinstance(arg_type, last.Type) and isinstance(arg_type.base, last.Struct):
            # Find __next__() func for type and determine its return type
            return self.result_type_of_method(arg_type, '__next__', errnode=expr)
          else:
            assert False, "todo"

        ste_in_globals = self.globals.get(expr.func.name)
        in_globals = ste_in_globals.ref_node
        if isinstance(in_globals, last.FuncDef):
          if in_globals.rtype is _KEYWORDS['auto']:
            if not self.resolve_function_return_type(in_globals):
              # TODO: Returning None for recursive resolve_function_return_type()
              # seems dicey for general users of this function.
              # See extra HACK in last.Expr case below too.
              return None
          return in_globals.rtype
        elif isinstance(in_globals, last.Struct):
          return in_globals.cached_type()
        elif isinstance(in_globals, last.MacroDef):
          macro_expansion = self.expand_macro(expr, in_globals)
          return self.expr_type(funcdef, macro_expansion)
      elif isinstance(expr.func, last.GetAttr):
        lhs_type = self.expr_type(funcdef, expr.func.lhs)
        return self.result_type_of_method(lhs_type, expr.func.rhs, errnode=expr.func)
    elif isinstance(expr, last.CompExpr):
      assert len(expr.chain) == 3, "todo"
      if expr.chain[1].name in ('==', '!=', '<=', '<', '>', '>='):
        return _KEYWORDS['bool']
      assert False, "todo"
    elif isinstance(expr, last.Not):
      return _KEYWORDS['bool']
    elif isinstance(expr, last.UnaryExpr):
      rhs_type = self.expr_type(funcdef, expr.obj)
      if expr.op.name == '*':
        if not isinstance(rhs_type, last.PointerDecl):
          self.error_at(expr.obj, 'expecting pointer type for dereference')
        return rhs_type.base
      elif expr.op.name == '&':
        # TODO: lval context
        return last.PointerDecl(rhs_type)
      elif expr.op.name == '-' and rhs_type is _KEYWORDS['i32']:
        return _KEYWORDS['i32']
      else:
        assert False, "unhandled unary op %s" % expr.op
    elif isinstance(expr, last.Ident):
      if ste := funcdef.find_in_symtab(expr.name):
        return ste.type
      if ste := self.globals.get(expr.name):
        return ste.type
      assert False, "unhandled Ident expr_type %s" % expr
    elif isinstance(expr, last.Expr):
      t0 = self.expr_type(funcdef, expr.chain[0])
      print('EXPRt0', t0)
      print('EXPRt2', self.expr_type(funcdef, expr.chain[2]))
      if t0 is None: return None  # HACK for recursive expr_type, see also in FuncCall.
      for i in range(1, len(expr.chain), 2):
        if (expr.chain[i].name not in ('+', '*', '-', '/') or
            self.expr_type(funcdef, expr.chain[i+1]) is not t0):
          break
      else:
        return t0
    elif isinstance(expr, last.Cast):
      return expr.type
    elif isinstance(expr, last.ListDecl):
      assert False, str(expr)
    elif isinstance(expr, last.ListComprehension):
      elem_type = self.expr_type(funcdef, expr.body.result)
      return self.get_list_struct_for_contained_type(elem_type)
    elif isinstance(expr, last.List):
      # Initial visit to create struct does other error checks.
      elem_type = self.expr_type(funcdef, expr.values[0])
      return self.get_list_struct_for_contained_type(elem_type)
    elif isinstance(expr, last.GetAttr):
      lhs = self.expr_type(funcdef, expr.lhs)
      # XXX Type vs Struct again
      if isinstance(lhs, last.Type):
        cur = lhs.base
      else:
        cur = lhs
      while isinstance(cur, last.PointerDecl):
        cur = cur.base
      if isinstance(cur, str):
        if expr.rhs == 'ptr':
          return last.PointerDecl(_KEYWORDS['i8'])
        elif expr.rhs == 'len':
          return _KEYWORDS['i64']
        self.error_at(expr, '"%s" not found on "%s"' % (expr.rhs, cur))
        return None
      else:
        assert isinstance(cur, last.Struct), str(cur)
        for x in cur.members:
          if x.name == expr.rhs:
            return x.type
        else:
          self.error_at(expr, '"%s" not found on "%s"' % (expr.rhs, cur.name))
          return None
    elif isinstance(expr, last.And) or isinstance(expr, last.Or) or isinstance(expr, last.Not):
      return _KEYWORDS['bool']
    elif isinstance(expr, last.GetItem):
      obj = self.expr_type(funcdef, expr.obj)
      # XXX Type vs Struct
      if isinstance(obj, last.PointerDecl):
        return obj.base
      else:
        if isinstance(obj, last.ListDecl):
          return obj.base
        elif isinstance(obj, last.Struct):
          return self.result_type_of_method(obj, '__getitem__', errnode=expr)
        elif isinstance(obj, last.Type) and isinstance(obj.base, last.Struct):
          return self.result_type_of_method(obj.base, '__getitem__', errnode=expr)
        else:
          assert False, "todo; GetItem: " + str(obj)
    elif isinstance(expr, last.Tuple):
      return self.tuple_struct_for_values(funcdef, expr.items).cached_type()
    elif isinstance(expr, last.TupleDecl):
      assert False, str(expr)
    elif isinstance(expr, last.Type):
      return expr  # This is needed for sizeof(), not sure if it's a good idea here.
    assert False, "unhandled expr_type %s" % expr

  def resolve_function_return_type(self, fd):
    if getattr(fd, 'resolving_return_type', None):
      return False
    setattr(fd, 'resolving_return_type', True)
    self.resolve_idents(fd)
    returns = self.find_return_stmts(fd.body)
    if not returns:
      fd.rtype = _KEYWORDS['void']
    else:
      auto = _KEYWORDS['auto']
      return_type = auto
      for r in returns:
        this_type = self.expr_type(fd, r.value)
        if this_type is None:
          continue # Recursive function (e.g. test/run/type_resolve_params.luv)
        if return_type is auto:
          return_type = this_type
        elif return_type != this_type:
          self.error_at(r, 'returning "%s", previously "%s"' % (this_type, return_type))
      fd.rtype = return_type or _KEYWORDS['void']
    delattr(fd, 'resolving_return_type')
    return True

  def determine_all_auto_function_returns(self):
    func_defs = self.find_func_defs(self.ast_root)
    for fd in func_defs:
      if fd.rtype is _KEYWORDS['auto']:
        ret = self.resolve_function_return_type(fd)
        if not ret or fd.rtype is _KEYWORDS['auto']:
          assert isinstance(fd.name, last.Ident)
          self.error_at(fd, 'couldn\'t resolve return type for "%s"' % fd.name.name)

  def infer_types(self):
    self.determine_all_auto_function_returns()

  def get_c_type(self, node):
    assert node is not _KEYWORDS['auto']
    if node == _KEYWORDS['i8']:
      return 'int8_t'
    if node == _KEYWORDS['i16']:
      return 'int16_t'
    if node == _KEYWORDS['i32']:
      return 'int32_t'
    if node == _KEYWORDS['i64']:
      return 'int64_t'
    if node == _KEYWORDS['u8']:
      return 'uint8_t'
    if node == _KEYWORDS['u16']:
      return 'uint16_t'
    if node == _KEYWORDS['u32']:
      return 'uint32_t'
    if node == _KEYWORDS['u64']:
      return 'uint64_t'
    if node == _KEYWORDS['bool']:
      return '_Bool'
    if node == _KEYWORDS['void']:
      return 'void'
    if node == _KEYWORDS['cvoid']:
      return 'const void'
    if node == _KEYWORDS['f16']:
      return '_Float16'  # TODO: __bf16 too?
    if node == _KEYWORDS['f32']:
      return 'float'
    if node == _KEYWORDS['f64']:
      return 'double'
    if node == _KEYWORDS['str']:
      return 'struct $Str'
    if isinstance(node, last.PointerDecl):
      return self.get_c_type(node.base) + '*'
    if isinstance(node, last.OptionalDecl):
      struct = self.generated_structs[self.get_mangled_c_type(node.base)].struct
      assert isinstance(struct.name, last.Ident)
      return 'struct ' + struct.name.name
    if isinstance(node, last.Struct):
      assert isinstance(node.name, last.Ident), str(node.name)  # Not TIdent
      return 'struct ' + node.name.name
    if isinstance(node, last.ListDecl):
      struct = self.generated_structs[self.get_mangled_c_type(node.base)].struct
      assert isinstance(struct.name, last.Ident)
      return 'struct ' + struct.name.name
    if isinstance(node, last.TupleDecl):
      struct = self.tuple_struct_for_types(node.base)
      return 'struct ' + struct.name.name
    if isinstance(node, last.Type):
      # TODO: This should probably only be for a special BaseType, because for
      # subclasses of Type, this is wrong and confusing.
      return self.get_c_type(node.base)
    print('GET_C_TYPE', node)
    return '??/*%s*/' % node

  def get_mangled_c_type(self, node):
    #print('GET_MANGLED_C_TYPE', node)
    x = self.get_c_type(node)
    x = x.replace('struct ', '')
    return x

  def get_safe_c_name(self, luv_name):
    # TODO
    return luv_name

  def sigils_for_indir(self, node_for_err, count):
    if count >= 2:
      self.error_at(node_for_err, "taking address of lvalue")
    if count == 1:
      return '&'
    if count == 0:
      return ''
    if count < 0:
      return '*'*(-count)

  def expr(self, node):
    if isinstance(node, last.Ident):
      ste = self.current_function.find_in_symtab(node.name) if self.current_function else None
      if ste:
        if ste.is_upval:
          return '*$up->%s' % self.get_safe_c_name(node.name)
        return self.get_safe_c_name(node.name)
      else:
        # "special" means just emit the ident literally, even if undefined.
        if not self.globals.get(node.name) and not node.special:
          self.error_at(node, '%s undefined' % node.name)
        return self.get_safe_c_name(node.name)
    elif isinstance(node, last.Number):
      if isinstance(node.value, int):
        return 'int32_t$__lit__(%s)' % node.value  # TODO: unsigned and size suffixes
      elif isinstance(node.value, float):
        # TODO: double vs. float based on ... size?
        return 'double$__lit__(%s)' % node.value
      else:
        assert False, "unhandled Number type %s" % node
    elif isinstance(node, last.String):
      return '$Str$__lit__(\"%s\")' % node.value
    elif isinstance(node, last.Const):
      if node.name == 'false':
        return '(/*false*/0)'
      elif node.name == 'true':
        return '(/*true*/1)'
      elif node.name == 'null':
        return '(/*null*/(void*)0)'
      else:
        assert False, "unhandled Const %s" % node
    elif isinstance(node, last.CompExpr):
      assert len(node.chain) == 3, "todo chained"
      # TODO: passing op right through
      return '(%s) %s (%s)' % (
          self.expr(node.chain[0]), node.chain[1].name, self.expr(node.chain[2]))
    elif isinstance(node, last.UnaryExpr):
      assert isinstance(node.op, last.Op) and node.op.name in ('&', '-', '+', '~', '*')
      return node.op.name + '(' + self.expr(node.obj) + ')'
    elif isinstance(node, last.GetAttr):
      lhs_type = self.expr_type(self.current_function, node.lhs)
      indirs = 0
      while isinstance(lhs_type, last.PointerDecl):
        lhs_type = lhs_type.base
        indirs -= 1
      return '(%s(%s)).%s' % (self.sigils_for_indir(node, indirs), self.expr(node.lhs), node.rhs)
    elif isinstance(node, last.GetItem):
      ty = self.expr_type(self.current_function, node.obj)
      # If x is a pointer, assume x[n] means like C, not __getitem__(x[0], n) as
      # it could also in theory mean (or some other level of indirection into
      # ***p).
      if isinstance(ty, last.PointerDecl):
        return '%s[%s]' % (self.expr(node.obj), self.expr(node.index))
      else:
        c_type = self.get_mangled_c_type(ty)
        return '%s$__getitem__(%s%s, %s)' % (
            c_type,
            self.sigils_for_indir(node, 0),
            self.expr(node.obj),
            self.expr(node.index))
    elif isinstance(node, last.FuncCall):
      if isinstance(node.func, last.Ident) and node.func.name == 'iter':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return '%s$__iter__(&%s)' % (self.get_mangled_c_type(arg_type), self.expr(node.args[0]))
        else:
          self.error_at(node.func, 'incorrect number of arguments to "iter"')

      if isinstance(node.func, last.Ident) and node.func.name == 'sizeof':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return 'sizeof(%s)' % self.get_c_type(arg_type)
        else:
          self.error_at(node.func, 'incorrect number of arguments to "sizeof"')

      if isinstance(node.func, last.Ident) and node.func.name == 'zeroed':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return '(%s){0}' % self.get_c_type(arg_type)
        else:
          self.error_at(node.func, 'incorrect number of arguments to "zeroed"')

      if isinstance(node.func, last.Ident) and node.func.name == 'unreachable':
        if len(node.args) == 0:
          return '({__builtin_unreachable(); assert(0);})'
        else:
          self.error_at(node.func, 'incorrect number of arguments to "unreachable"')

      if isinstance(node.func, last.Ident) and node.func.name == 'hash':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return '%s$__hash__(%s)' % (self.get_mangled_c_type(arg_type), self.expr(node.args[0]))
        else:
          self.error_at(node.func, 'incorrect number of arguments to "hash"')

      if isinstance(node.func, last.Ident) and node.func.name == 'next':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return '%s$__next__(&%s)' % (self.get_mangled_c_type(arg_type), self.expr(node.args[0]))
        else:
          self.error_at(node.func, 'incorrect number of arguments to "next"')

      self_inject = []
      if isinstance(node.func, last.GetAttr):
        lhs_type = self.expr_type(self.current_function, node.func.lhs)
        if lhs_type is None and isinstance(node.func.lhs, last.Ident):
          # Package.
          global_sym = self.globals.get(node.func.lhs.name)
          assert global_sym
          package = global_sym.ref_node
          assert isinstance(package, last.Package)
          result = ''
          if x := package.globals.get(node.func.rhs):
            ident = last.Ident(node.func.rhs)
            ident.special = True
            result = self.expr(ident)
          else:
            self.error_at(node, '%s not found in %s' % (node.func.rhs, package.name))
            return ''
        else:
          # Pseudo member function.
          # LHS might be a ****Struct, or *Struct, or Struct, so first find the
          # underlying Struct type.
          lhs = node.func.lhs
          while True:
            # TODO: this is dumb, PointerDecl is a Type with a base of Struct,
            # but Structs are Types with a base of Struct. I think Struct should
            # just be a Type. (i.e. can't first test for "is Type and base is
            # Struct", because then it'll break on a pointer to the struct.)
            if lhs_type.__class__ is last.Type and isinstance(lhs_type.base, last.Struct):
              break
            if isinstance(lhs_type, last.PointerDecl):
              lhs_type = lhs_type.base
              # XXX Type vs Struct
              if isinstance(lhs_type, last.Struct):
                lhs_type = last.Type(lhs_type)
              lhs = last.UnaryExpr(last.Op('*'), lhs)
          else:
            self.error_at(node, '%s not callable on %s' % (node.func.rhs, node.func.lhs))
            return ''

          result_type = self.result_type_of_method(lhs_type, node.func.rhs, errnode=node.func)
          single_ptr_to = last.UnaryExpr(last.Op('&'), lhs)
          self_inject.append(single_ptr_to)
          result = self.method_name(lhs_type, node.func.rhs)
      else:
        result = self.expr(node.func)

      result += '('

      upvals = []
      if self.current_function:
        if isinstance(node.func, last.Ident):
          # TODO: this is obviously suck
          has_uv = self.current_function.upval_bindings.get(node.func.name)
          if has_uv:
            # We don't want to put $uv0, etc. into local function scope, so hack
            # with special=True to tell the lookup mechanism to emit it
            # literally even though it's undefined.
            uv_binding_local_name = last.Ident(has_uv.parent_binding_name)
            uv_binding_local_name.special = True
            upvals.append(last.UnaryExpr(last.Op('&'), uv_binding_local_name))

      result += ','.join(self.expr(x) for x in (upvals + self_inject + node.args))
      result += ')'
      return result
    elif isinstance(node, last.ListComprehension):
      result = '({'
      list_type = self.expr_type(self.current_function, node)
      result_tmp = get_tmp_var()
      result_list_type = self.get_c_type(list_type)
      result_mangled_c_type = self.get_mangled_c_type(list_type)
      result += '%s %s = {0};' % (result_list_type, result_tmp)
      for f in node.body.fors:
        iter_tmp = get_tmp_var()
        thing_tmp = get_tmp_var()
        it_ret_tmp = get_tmp_var()

        thing_type = self.expr_type(self.current_function, f.thing)
        thing_c_type = self.get_c_type(thing_type)
        # TODO: not sure about make a local copy of the thing (i.e. `range(5)`)
        result += '%s %s = %s;' % (thing_c_type, thing_tmp, self.expr(f.thing))
        thing_mangled_c_type = self.get_mangled_c_type(thing_type)
        iter_type = self.result_type_of_method(thing_type, '__iter__', node)
        iter_mangled_c_type = self.get_mangled_c_type(iter_type)
        result += 'struct %s %s = %s$__iter__(&%s);' % (
            iter_mangled_c_type, iter_tmp, thing_mangled_c_type, thing_tmp)

        assert isinstance(f.its, last.Ident), "todo"
        it_name = f.its.name
        iter_return_type = self.result_type_of_method(iter_type, '__next__', node)
        iter_return_c_type = self.get_c_type(iter_return_type)
        assert (isinstance(iter_return_type, last.Type) and
                isinstance(iter_return_type.base, last.Struct))
        assert iter_return_type.base.members[1].name == '_1'
        iter_value_type = iter_return_type.base.members[1].type
        iter_value_c_type = self.get_c_type(iter_value_type)

        self.current_function.push_empty_symtab_scope()
        self.current_function.add_to_symtab(it_name, last.SymTabEntry(iter_value_type,
          f.its, is_declared_local=True))

        result += '%s %s = {0};' % (iter_return_c_type, it_ret_tmp)
        result += 'for(;;) {'
        result += '%s = %s$__next__(&%s);' % (
            it_ret_tmp, iter_mangled_c_type, iter_tmp)
        result += 'if (!(%s._0)) break;' % it_ret_tmp
        result += '%s %s = %s._1;' % (iter_value_c_type, it_name, it_ret_tmp)

        result += '%s$append(&%s, %s);' % (
            result_mangled_c_type, result_tmp, self.expr(node.body.result))
        result += '}'

        self.current_function.pop_symtab_scope()

      result += result_tmp + ';'
      result += '})'
      return result
    elif isinstance(node, last.List):
      result = '({'
      list_type = self.expr_type(self.current_function, node)
      tmp_list = get_tmp_var()
      result += '%s %s = {0};' % (self.get_c_type(list_type), tmp_list)
      mangled_list_type = self.get_mangled_c_type(list_type)
      result += '%s$reserve(&%s, %s);' % (mangled_list_type, tmp_list, len(node.values))
      for v in node.values:
        result += '%s$append(&%s, %s);' % (mangled_list_type, tmp_list, self.expr(v))
      result += '%s;' % tmp_list
      return result + '})'
    elif isinstance(node, last.Expr):
      result = '({'
      i = 1
      cur_l = node.chain[0]
      cur_op = node.chain[i]
      cur_r = node.chain[i+1]
      while True:
        l_type = self.expr_type(self.current_function, cur_l)
        r_type = self.expr_type(self.current_function, cur_r)
        if l_type is not r_type:
          self.error_at(node, 'can\'t "%s" with lhs=%s, rhs=%s' % (cur_op, l_type, r_type))
        c_type = self.get_c_type(l_type)
        tmp = get_tmp_var()
        tmp_ident = last.Ident(tmp)
        self.current_function.add_to_symtab(tmp, last.SymTabEntry(
            l_type, cur_op, is_compiler_temporary=True))
        mangled_c_type = self.get_mangled_c_type(l_type)
        result += '%s %s = %s$%s(%s, %s);' % (
            c_type, tmp, mangled_c_type, OP_MAP[cur_op.name], self.expr(cur_l), self.expr(cur_r))

        cur_l = tmp_ident
        i += 2
        if i >= len(node.chain):
          break
        cur_op = node.chain[i]
        cur_r = node.chain[i+1]
      result += cur_l.name + ';})'
      return result
    elif isinstance(node, last.Tuple):
      struct = self.tuple_struct_for_values(self.current_function, node.items)
      return '(struct %s){' % struct.name.name + ','.join(self.expr(v) for v in node.items) + '}'
    elif isinstance(node, last.And):
      return '&&'.join(self.expr(x) for x in node.tests)
    elif isinstance(node, last.Or):
      return '||'.join(self.expr(x) for x in node.tests)
    elif isinstance(node, last.Not):
      return '!(%s)' % self.expr(node.expr)
    elif isinstance(node, last.Cast):
      return '((%s)(%s))' % (self.get_c_type(node.type), self.expr(node.expr))
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
      if isinstance(node.cond, last.OptionalUnwrap):
        result = 'if ((%s).has) {' % self.expr(node.cond.optexpr)
        opttype = self.expr_type(self.current_function, node.cond.optexpr)
        assert isinstance(opttype, last.OptionalDecl)
        result += '%s %s = (%s).val;' % (
            self.get_c_type(opttype.base), node.cond.bind.name, self.expr(node.cond.optexpr))
        result += self.stmt(node.body)
        result += '}'
      else:
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
        result += 'else'
        result += self.stmt(node.els)
      return result
    elif isinstance(node, last.For):
      coll_tmp = get_tmp_var()
      coll_type = self.expr_type(self.current_function, node.collection)
      coll_c_type = self.get_c_type(coll_type)
      coll_mangled_c_type = self.get_mangled_c_type(coll_type)
      iter_tmp = get_tmp_var()
      it_ret_tmp = get_tmp_var()
      result = '%s %s = %s;' % (coll_c_type, coll_tmp, self.expr(node.collection))
      iter_type = self.result_type_of_method(coll_type, '__iter__', node)
      iter_c_type = self.get_c_type(iter_type)
      iter_mangled_c_type = self.get_mangled_c_type(iter_type)
      result += '%s %s = %s$__iter__(&%s);' % (
          iter_c_type, iter_tmp, coll_mangled_c_type, coll_tmp)
      assert isinstance(node.it, last.Ident), "todo"
      it_name = node.it.name
      iter_return_type = self.result_type_of_method(iter_type, '__next__', node)
      iter_return_c_type = self.get_c_type(iter_return_type)
      assert (isinstance(iter_return_type, last.Type) and
              isinstance(iter_return_type.base, last.Struct))
      assert iter_return_type.base.members[1].name == '_1'
      iter_value_type = iter_return_type.base.members[1].type
      iter_value_c_type = self.get_c_type(iter_value_type)
      result += '%s %s = {0};' % (iter_return_c_type, it_ret_tmp)
      result += 'for(;;) {'
      result += '%s = %s$__next__(&%s);' % (it_ret_tmp, iter_mangled_c_type, iter_tmp)
      result += 'if (!(%s._0)) break;' % it_ret_tmp
      result += '%s %s = %s._1;' % (iter_value_c_type, it_name, it_ret_tmp)
      result += self.stmt(node.body)
      result += '}'
      return result
    elif isinstance(node, last.While):
      assert node.els is None, 'todo'
      result = 'while(%s){' % self.expr(node.cond)
      result += self.stmt(node.body)
      result += '}'
      return result
    elif isinstance(node, last.Return):
      result = 'return'
      if node.value:
        result += ' ' + self.expr(node.value)
      result += ';'
      return result
    elif isinstance(node, last.Break):
      return 'break;'
    elif isinstance(node, last.Pass):
      return ';'
    elif isinstance(node, last.Del):
      result = ''
      for x in node.exprs:
        type = self.expr_type(self.current_function, x)
        c_type = self.get_mangled_c_type(type)
        result += '%s$__del__(&%s);' % (c_type, self.expr(x))
      return result
    elif isinstance(node, last.Assign):
      if isinstance(node.lhs, last.Tuple):
        assert all(isinstance(x, last.Ident) for x in node.lhs.items)
        rhs_type = self.expr_type(self.current_function, node.rhs)
        if isinstance(rhs_type, last.Type) and isinstance(rhs_type.base, last.Struct):
          field_types = [x.type for x in rhs_type.base.members]
        elif isinstance(rhs_type, last.TupleDecl):
          field_types = [x for x in rhs_type.base]
        else:
          assert False, "todo; tuple style?"
        struct = self.tuple_struct_for_types(field_types)
        tmp = get_tmp_var()
        assert isinstance(struct.name, last.Ident)
        result = 'struct %s %s = %s;\n' % (struct.name.name, tmp, self.expr(node.rhs))
        for i, x in enumerate(node.lhs.items):
          result += '%s = %s._%d;' % (x.name, tmp, i)
        return result
      else:
        lhs_type = self.expr_type(self.current_function, node.lhs)
        lhs = self.expr(node.lhs)
        rhs = self.expr(node.rhs)
        if isinstance(lhs_type, last.OptionalDecl):
          if isinstance(node.rhs, last.Const) and node.rhs.name == 'null':
            return '%s = (%s){/*has*/0};' % (lhs, self.get_c_type(lhs_type))
          else:
            return '%s = (%s){/*has*/1,/*val*/%s};' % (lhs, self.get_c_type(lhs_type), rhs)
        else:
          return '%s = %s;' % (lhs, rhs)
    elif isinstance(node, last.AugAssign):
      lhs_type = self.expr_type(self.current_function, node.lhs)
      lhs_c_type = self.get_mangled_c_type(lhs_type)
      lhs = self.expr(node.lhs)
      rhs = self.expr(node.rhs)
      return '%s$%s(&%s, %s);' % (lhs_c_type, OP_MAP[node.op.name], lhs, rhs)
    elif isinstance(node, last.VarDecl):
      if node.init:
        rhs = self.expr(node.init)
        lhs = self.get_safe_c_name(node.name)
        lhs_type = self.get_c_type(node.type)
        if isinstance(node.type, last.OptionalDecl):
          if isinstance(node.init, last.Const) and node.init.name == 'null':
            return '%s = (%s){/*has*/0};' % (lhs, lhs_type)
          else:
            return '%s = (%s){/*has*/1,/*val*/%s};' % (lhs, lhs_type, rhs)
        else:
          return '%s = %s;' % (lhs, rhs)
      else:
        return ''
    elif isinstance(node, last.Assert):
      # clang-format is de-wrapping the `if` if there's no comment?
      result = '#ifndef NDEBUG // assert\nif (!(%s)){' % self.expr(node.expr)
      if node.message is not None:
        result += 'printf("%s\n");' % self.expr(node.message)
      result += 'assert(0);}\n#endif  // assert NDEBUG\n'
      return result
    elif isinstance(node, last.Nonlocal):
      return '/* NONLOCAL %s */;' % ', '.join(node.vars)
    elif isinstance(node, last.FuncDef):
      return '/* HOISTED %s */;' % node.name
    elif isinstance(node, last.Import):
      return '/* TODO: import in body */'
    elif isinstance(node, last.ImportFrom):
      return '/* TODO: from import in body */'
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
    assert isinstance(func.name, last.Ident)
    fname = self.get_safe_c_name(func.name.name)
    if fname == 'main':
      rtype = 'int'
    else:
      rtype = self.get_c_type(func.rtype)
    # TODO: hidden are hoisted funcs, which should be static, but also need an
    # indication of exported/not at syntax level.
    is_static = 'static ' if func.hidden else ''
    return '%s%s %s(%s)' % (is_static, rtype, fname, params)

  def function_definition(self, func):
    if len(func.body.entries) == 1 and isinstance(func.body.entries[0], last.External):
      assert isinstance(func.name, last.Ident)
      return '\n// %s was external\n' % func.name.name
    result = self.function_forward_declaration(func)
    self.current_function = func
    result += '{'
    # There can be more than one in the body of list comprehensions, but not
    # here at the beginning of a function body.
    assert len(func.symtabs) == 1
    for n, ste in func.symtabs[0].items():
      if ste.is_declared_local and not ste.is_hoisted_function:
        if ste.type is _KEYWORDS['void']:
          self.error_at(ste.ref_node, 'can\'t declare local of type "%s"' % ste.type.base)
        result += '%(type)s %(name)s = (%(type)s){0};' % {
            'type': self.get_c_type(ste.type), 'name': self.get_safe_c_name(n)}
    for n, upval in func.upval_bindings.items():
      result += 'struct %s %s = {' % (upval.struct_name, upval.parent_binding_name)
      for name, uv in upval.to_bind.items():
        in_cur_func = func.symtabs[0][name]
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
    # TODO: probably homogenize this with user structs.
    for n, uvb in obj.upval_bindings.items():
      result += 'struct %s {' % uvb.struct_name
      for name, uv in uvb.to_bind.items():
        result += '%s* %s;' % (self.get_c_type(uv.type), self.get_safe_c_name(name))
      result += '};\n'
    return result

  def generate_struct(self, obj):
    assert isinstance(obj, last.Struct)
    assert isinstance(obj.name, last.Ident)
    result = '\nstruct %s {\n' % obj.name.name
    for field in obj.members:
      result += '%s %s;\n' % (self.get_c_type(field.type), self.get_safe_c_name(field.name))
    result += '};\n'
    return result

  def generate_struct_constructor(self, obj):
    assert isinstance(obj, last.Struct)
    assert isinstance(obj.name, last.Ident)
    name = obj.name.name
    if obj.omit_constructor:
      return ''
    result = '\nstruct %s %s(' % (name, name)
    for i,field in enumerate(obj.members):
      result += '%s %s' % (self.get_c_type(field.type), self.get_safe_c_name(field.name))
      if i < len(obj.members) - 1:
        result += ','
    result += '){\n'
    result += 'struct %s $_ = {0};\n' % name
    for field in obj.members:
      n = self.get_safe_c_name(field.name)
      result += '$_.%s = %s;\n' % (n, n)
    result += 'return $_;'
    result += '}\n'
    return result

  def topo_struct_sort(self, structs):
    L = []

    def visit(n):
      if hasattr(n, 'topo_permanent'):
        return
      if hasattr(n, 'topo_temporary'):
        assert isinstance(n.name, last.Ident)
        self.error_at(n, 'recursive struct definition for "%s"' % n.name.name)
        return

      n.topo_temporary = True

      for mem in n.members:
        if isinstance(mem.type, last.Type) and isinstance(mem.type.base, last.Struct):
          visit(mem.type.base)

      del n.topo_temporary
      n.topo_permanent = True
      L.append(n)

    for s in structs:
      if hasattr(s, 'topo_permanant'):
        continue
      visit(s)

    return L

  def compile(self, outfn):
    with open(outfn, 'w', newline='\n') as f:
      f.write(r'''#include <stdint.h>
#include <assert.h>

void* malloc(size_t);
void free(void*);
void* memcpy(void*, const void*, uint64_t);
int printf(const char *, ...);

/* <MIT License>
 Copyright (c) 2013  Marek Majkowski <marek@popcount.org>
 https://github.com/majek/csiphash/
*/
/* Modified to assume little-endian. */

#define CSIP_ROTATE(x, b) (uint64_t)( ((x) << (b)) | ( (x) >> (64 - (b))) )

#define CSIP_HALF_ROUND(a,b,c,d,s,t)      \
  a += b; c += d;                         \
  b = CSIP_ROTATE(b, s) ^ a;              \
  d = CSIP_ROTATE(d, t) ^ c;              \
  a = CSIP_ROTATE(a, 32);

#define CSIP_DOUBLE_ROUND(v0,v1,v2,v3)    \
  CSIP_HALF_ROUND(v0,v1,v2,v3,13,16);     \
  CSIP_HALF_ROUND(v2,v1,v0,v3,17,21);     \
  CSIP_HALF_ROUND(v0,v1,v2,v3,13,16);     \
  CSIP_HALF_ROUND(v2,v1,v0,v3,17,21);


static uint64_t siphash24(const void *src, unsigned long src_sz, const char key[16]) {
  const uint64_t *_key = (uint64_t *)key;
  uint64_t k0 = (uint64_t)(_key[0]);
  uint64_t k1 = (uint64_t)(_key[1]);
  uint64_t b = (uint64_t)src_sz << 56;
  const uint64_t *in = (uint64_t*)src;

  uint64_t v0 = k0 ^ 0x736f6d6570736575ULL;
  uint64_t v1 = k1 ^ 0x646f72616e646f6dULL;
  uint64_t v2 = k0 ^ 0x6c7967656e657261ULL;
  uint64_t v3 = k1 ^ 0x7465646279746573ULL;

  while (src_sz >= 8) {
    uint64_t mi = (uint64_t)(*in);
    in += 1; src_sz -= 8;
    v3 ^= mi;
    CSIP_DOUBLE_ROUND(v0,v1,v2,v3);
    v0 ^= mi;
  }

  uint64_t t = 0; uint8_t *pt = (uint8_t *)&t; uint8_t *m = (uint8_t *)in;
  switch (src_sz) {
  case 7: pt[6] = m[6];
  case 6: pt[5] = m[5];
  case 5: pt[4] = m[4];
  case 4: *((uint32_t*)&pt[0]) = *((uint32_t*)&m[0]); break;
  case 3: pt[2] = m[2];
  case 2: pt[1] = m[1];
  case 1: pt[0] = m[0];
  }
  b |= (uint64_t)(t);

  v3 ^= b;
  CSIP_DOUBLE_ROUND(v0,v1,v2,v3);
  v0 ^= b; v2 ^= 0xff;
  CSIP_DOUBLE_ROUND(v0,v1,v2,v3);
  CSIP_DOUBLE_ROUND(v0,v1,v2,v3);
  return (v0 ^ v1) ^ (v2 ^ v3);
}

static const char csip_key[16] = "luv.2024-02-23.";

struct $Str {
  int8_t* ptr;
  int64_t len;
};

#define $Str$__lit__(s) (struct $Str){(int8_t*)s, sizeof(s) - 1}

struct $Str $Str$from_n(char* data, size_t len) {
  struct $Str s = {malloc(len + 1), len};
  memcpy(s.ptr, data, len + 1);
  return s;
}
struct $Str $Str$__add__(struct $Str a, struct $Str b) {
  char* p = malloc(a.len + b.len + 1);
  memcpy(p, a.ptr, a.len);
  memcpy(p + a.len, b.ptr, b.len + 1);
  return (struct $Str){(int8_t*)p, a.len + b.len};
}
void $Str$__del__(struct $Str* self) {
  free(self->ptr);
}
uint64_t $Str$__hash__(struct $Str self) {
  return siphash24(self.ptr, self.len, csip_key);
}
#define $Str$__getitem__(a, b) (a[b])

#define double$__lit__(a) (a)
#define double$__del__(a)

#define int32_t$__lit__(a) (a)
#define int32_t$__del__(a)
#define int32_t$__add__(a, b) ((a)+(b))
#define int32_t$__sub__(a, b) ((a)-(b))
#define int32_t$__mul__(a, b) ((a)*(b))
#define int32_t$__div__(a, b) ((a)/(b))
#define int32_t$__mod__(a, b) ((a)%(b))
#define int32_t$__iadd__(a, b) ((*a)+=(b))
#define int32_t$__isub__(a, b) ((*a)-=(b))
#define int32_t$__imul__(a, b) ((*a)*=(b))
#define int32_t$__idiv__(a, b) ((*a)/=(b))
#define int32_t$__imod__(a, b) ((*a)%=(b))
#define int32_t$__hash__(a) ((uint64_t)(a))

#define int64_t$__lit__(a) (a)
#define int64_t$__del__(a)
#define int64_t$__add__(a, b) ((a)+(b))
#define int64_t$__sub__(a, b) ((a)-(b))
#define int64_t$__mul__(a, b) ((a)*(b))
#define int64_t$__div__(a, b) ((a)/(b))
#define int64_t$__mod__(a, b) ((a)%(b))
#define int64_t$__iadd__(a, b) ((*a)+=(b))
#define int64_t$__isub__(a, b) ((*a)-=(b))
#define int64_t$__imul__(a, b) ((*a)*=(b))
#define int64_t$__idiv__(a, b) ((*a)/=(b))
#define int64_t$__imod__(a, b) ((*a)%=(b))
#define int64_t$__hash__(a) ((uint64_t)(a))

static void printi32(int32_t x) {
  printf("%d", x);
}
static void printi64(int64_t x) {
  printf("%lld", x);
}
static void printu64(uint64_t x) {
  printf("%llu", x);
}
static void printbool(_Bool x) {
  printf(x ? "true" : "false");
}
static void printstr(struct $Str s) {
  printf("%s", s.ptr);
}
static void printrawstr(int8_t* s) {
  printf("%s", s);
}
static void printspace(void) {
  printf(" ");
}
static void printnl(void) {
  printf("\n");
}
''')

      def header(s):
        f.write('\n\n')
        f.write('// ' + '-'*77 + '\n')
        f.write('// ' + s + '\n')
        f.write('// ' + '-'*77 + '\n')

      all_structs = [ste.ref_node for n,ste in self.globals.items()
                     if isinstance(ste.ref_node, last.Struct)]
      sorted_structs = self.topo_struct_sort(all_structs)

      header('struct decls')
      for obj in sorted_structs:
        f.write(self.generate_struct(obj))

      if self.have_error: return

      header('struct constructors')
      for obj in sorted_structs:
        f.write(self.generate_struct_constructor(obj))

      if self.have_error: return

      header('upval structs')
      for n,ste in self.globals.items():
        obj = ste.ref_node
        if isinstance(obj, last.FuncDef):
          f.write(self.generate_upval_struct(obj))

      if self.have_error: return

      header('function forward decls')
      for n,ste in self.globals.items():
        obj = ste.ref_node
        if isinstance(obj, last.FuncDef):
          f.write(self.function_forward_declaration(obj))
          f.write(';\n')
        elif isinstance(obj, last.Package):
          for name,item_ste in obj.globals.items():
            item = item_ste.ref_node
            # TODO: more than just extern functions
            if (isinstance(item, last.FuncDef) and len(item.body.entries) == 1 and
                isinstance(item.body.entries[0], last.External)):
              f.write(self.function_forward_declaration(item))
              f.write(';\n')

      if self.have_error: return

      header('globals')
      for n,ste in self.globals.items():
        obj = ste.ref_node
        if isinstance(obj, last.VarDecl):
          if obj.type is _KEYWORDS['void']:
            self.error_at(obj, 'can\'t declare global of type "%s"' % obj.type.base)
          f.write('%(type)s %(name)s' % {
                'type': self.get_c_type(obj.type),
                'name': self.get_safe_c_name(obj.name)})
          if obj.init:
            f.write(' = %s' % self.expr(obj.init))
          f.write(';\n')

      if self.have_error: return

      header('function implementations')
      for n,ste in self.globals.items():
        obj = ste.ref_node
        if isinstance(obj, last.FuncDef):
          f.write(self.function_definition(obj))

      if self.have_error: return

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
    raise RuntimeError('dyibicc failed')
  return proc.stdout.rstrip('\n')

def do_tests(parser, test_list, update):
  if not test_list:
    test_list = sorted(glob.glob('test/**/*.luv', recursive=True))

  disabled_list = []
  passed_list = []
  err = None
  def tt_error_callback(node, msg):
    nonlocal err
    if err: return
    err = (node, msg)

  for t in test_list:
    if '.disabled.' in t:
      disabled_list.append(t)
      continue
    print(t)
    t = t.replace('\\', '/')
    source, expected = test_contents(t)
    is_parse = t.startswith('test/parse')
    is_type = t.startswith('test/type')
    tree = parser.parse(source, include_prelude=not is_parse and not is_type)
    #print(tree.pretty())
    ast = ToAst().transform(tree)
    #pprint.pprint(ast)
    if is_parse:
      got = pprint.pformat(ast)
    elif is_type:
      err = None
      c = Compiler(t, ast, parser, error_callback=tt_error_callback)
      c_file = os.path.splitext(t)[0] + '.c'
      c.compile(c_file)
      got = '!\n%s:%d:%d:%s' % (t, err[0].line, err[0].column, err[1])
    elif t.startswith('test/run'):
      c = Compiler(t, ast, parser)
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
  prelude = open('prelude.luv', 'r', newline='\n').read()
  parser = Parser(prelude)

  if len(sys.argv) >= 2 and sys.argv[1] == 'test':
    do_tests(parser, sys.argv[2:], update=False)
  elif len(sys.argv) >= 2 and sys.argv[1] == 'test_update':
    do_tests(parser, sys.argv[2:], update=True)
  else:
    source, _ = test_contents(sys.argv[1])
    tree = parser.parse(source + '\n')
    print(tree.pretty(), file=sys.stderr)

    ast = ToAst().transform(tree)
    pprint.pprint(ast, stream=sys.stderr)
    c = Compiler(sys.argv[1], ast, parser)
    c_file = os.path.splitext(sys.argv[1])[0] + '.c'
    c.compile(c_file)
    dyibicc(c_file)


if __name__ == '__main__':
  main()
