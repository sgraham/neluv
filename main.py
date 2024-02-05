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

  'false': last.Const('false'),
  'null': last.Const('null'),
  'true': last.Const('true'),

  'str': last.Type('str'),
}

_KEYWORDS['byte'] = _KEYWORDS['u8']
_KEYWORDS['double'] = _KEYWORDS['f64']
_KEYWORDS['float'] = _KEYWORDS['f32']
_KEYWORDS['int'] = _KEYWORDS['i32']

_RANGE_TYPE = last.RangeType(None)

visit_tag_counter = 0
tmp_var_counter = 0
OP_MAP = {
    '+': '__add__',
    '-': '__sub__',
    '*': '__mul__',
    '/': '__div__',
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
    return last.TupleCreate(children)

  def tuple(self, children):
    return last.TupleAssign(children)

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

  def optional_decl(self, children):
    return last.OptionalDecl(children[0])

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

  def del_stmt(self, children):
    return last.Del(children)

  def pass_stmt(self, children):
    return last.Pass()

  def nonlocal_stmt(self, children):
    return last.Nonlocal(children)

  def for_stmt(self, children):
    return last.For(children[0], children[1], children[2], children[3])

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

  def single_dot_name(self, children):
    return last.MethodName(children[0], children[1])

  def assign(self, children):
    return last.Assign(children[0], children[1])

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

  def import_macros_stmt(self, children):
    return last.ImportMacros(children[0])

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

    self.create_tuple_struct([_KEYWORDS['bool'], _KEYWORDS['i32']], None)  # For range().
    self.create_range_structs()

    self.HACK_generate_list_int32_methods = False  # TODO XXX

    self.ast_root = ast_root
    self.parser = parser

    #print('START ------------------')
    #pprint.pprint(self.ast_root)

    self.current_function = None

    self.find_globals()
    #print('AFTER FIND_GLOBALS ------------------')
    #pprint.pprint(self.ast_root)

    self.build_function_symtabs()
    #print('AFTER SYMTABS ------------------')
    #pprint.pprint(self.ast_root)

    self.hoist_nested_functions()
    #print('AFTER HOIST ------------------')
    #pprint.pprint(self.ast_root)

    self.resolve_idents()
    #print('AFTER RESOLVE IDENTS ------------------')
    #pprint.pprint(self.ast_root)

    self.infer_types()
    #print('AFTER INFER TYPES ------------------')
    #pprint.pprint(self.ast_root)

    for contained, gsi in self.generated_structs.items():
      self.globals[gsi.struct.name] = last.SymTabEntry(gsi.node, gsi.struct)

  def is_lexically_before(self, a, b):
    if a.line == b.line: return a.column < b.column
    return a.line < b.line

  class FuncSymTab:
    def __init__(self, func, parent):
      self.func = func
      self.parent = parent
      for p in func.params:
        assert isinstance(p, last.TypedVar)
        func.symtab[p.name] = last.SymTabEntry(p.type, p, is_func_param=True)

    def visit_VarDecl(self, node):
      x = self.func.symtab.get(node.name)
      if x:
        if x.is_pending_nonlocal and self.parent.is_lexically_before(node, x.ref_node):
          self.parent.error_at(node, 'name "%s" is used before nonlocal declaration' % node.name)
        else:
          self.parent.error_at(node,
              'redefinition of "%s" in "%s"' % (node.name, self.func.name))
      self.func.symtab[node.name] = last.SymTabEntry(node.type, node, is_declared_local=True)

    def visit_For(self, node):
      if isinstance(node.it, list):
        for x in node.it:
          self.local(x)
      else:
        assert isinstance(node.it, last.Ident)
        self.local(node.it)

    def local(self, ident):
      x = self.func.symtab.get(ident.name)
      if not x:
        self.func.symtab[ident.name] = last.SymTabEntry(
            _KEYWORDS['auto'], ident, is_declared_local=True)
      elif x.is_pending_nonlocal and self.parent.is_lexically_before(ident, x.ref_node):
        self.parent.error_at(ident,
            'name "%s" is used before nonlocal declaration' % ident.name)

    def visit_Assign(self, node):
      if isinstance(node.lhs, last.Ident):
        self.local(node.lhs)
      elif isinstance(node.lhs, last.TupleAssign):
        if all(isinstance(x, last.Ident) for x in node.lhs.targets):
          for x in node.lhs.targets:
            self.local(x)

  class ScanForNonlocal:
    def __init__(self, func, parent):
      self.func = func
      self.parent = parent
    def visit_Nonlocal(self, node):
      for name in node.vars:
        self.func.symtab[name] = last.SymTabEntry(None, node, is_pending_nonlocal=True)

  def build_function_symtabs(self):
    for f in self.find_func_defs(self.ast_root):
      self.Visit(self.ScanForNonlocal(f, self), f.body, do_not_cross_types=[last.FuncDef])
      self.Visit(self.FuncSymTab(f, self), f.body, do_not_cross_types=[last.FuncDef])

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

      node.tag_for_visit = self.visit_tag

      if self.do_not_cross_types:
        for dnct in self.do_not_cross_types:
          if isinstance(node, dnct):
            x = getattr(self.visitor, 'after_' + node.__class__.__name__, None)
            if x: x(node)
            return to_return

      for f in dataclasses.fields(node):
        field = getattr(node, f.name)

        if isinstance(field, last.AstNode):
          ret = self.impl(field)
          if ret is not None:
            setattr(node, f.name, ret)
        elif isinstance(field, list):
          for i, lx in enumerate(field):
            if isinstance(lx, last.AstNode):
              ret = self.impl(lx)
              if ret is not None:
                field[i] = ret

      x = getattr(self.visitor, 'after_' + node.__class__.__name__, None)
      if x: x(node)
      return to_return

  def insert_global_or_error(self, node):
    name = node.name
    if isinstance(name, last.MethodName):
      name = '%s__$__%s' % (name.struct, name.methodname)
    if self.globals.get(name):
      self.error_at(node, 'redefinition at global scope of "%s"' % name)
    ty = None
    if isinstance(node, last.VarDecl):
      ty = node.type
    self.globals[name] = last.SymTabEntry(ty, node, is_global=True)

  def load_macros(self, fn):
    glob = {}
    loc = {}
    rel_fn = os.path.join(os.path.split(self.filename)[0], fn)
    with open(rel_fn, 'r') as f:
      exec(f.read(), glob, loc)
    for name,func in loc.items():
      if inspect.isfunction(func):
        co_mem = inspect.getmembers(func.__code__)
        for n,v in co_mem:
          if n == 'co_argcount' and v == 1:
            for l,o in loc.items():
              func.__globals__[l] = o
            self.insert_global_or_error(last.MacroDef(name, func))
            break

  def find_globals(self):
    assert isinstance(self.ast_root, last.TopLevel), self.ast_root

    for tl in self.ast_root.body.entries:
      if (isinstance(tl, last.FuncDef) or
          isinstance(tl, last.VarDecl) or
          isinstance(tl, last.Struct)):
        self.insert_global_or_error(tl)
      elif isinstance(tl, last.Assign) and isinstance(tl.lhs, last.Ident):
        # Handled below.
        pass
      elif isinstance(tl, last.ImportMacros):
        self.load_macros(tl.filename.value)
      else:
        self.error_at(tl, 'unexpected at top level %s' % tl)

    for i, tl in enumerate(self.ast_root.body.entries):
      if isinstance(tl, last.Assign) and isinstance(tl.lhs, last.Ident):
        # Turn simple Assign into VarDecl at global scope
        x = last.VarDecl(self.expr_type(None, tl.rhs), tl.lhs.name, tl.rhs)
        x.copy_meta(tl)
        self.ast_root.body.entries[i] = x
        self.insert_global_or_error(x)
      # TODO: multiple return tuple assignments

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
            # TODO: more lax probably
            if resolved.ref_node and isinstance(resolved.ref_node, last.Struct):
              f.type = resolved.ref_node.cached_type()
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
              p.type = resolved.ref_node.cached_type()

  def find_func_defs(self, start, top_level_only=False):
    class FindFuncDef:
      def __init__(self): self.result = []
      def visit_FuncDef(self, node): self.result.append(node)
    finder = FindFuncDef()
    self.Visit(finder, start, do_not_cross_types=[last.FuncDef] if top_level_only else None)
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
        in_upper = f.symtab.get(i)
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
            func.symtab[i] = ste
            to_bind[i] = ste
            pending_non_local = pending_non_local_name = None
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
          old_name = nested.name
          new_name = old_name + '$%s' % cur.name
          nested.name = new_name

          to_bind = self.parent.find_upvals(nested, self.cur_func_stack + [nested])
          if to_bind:
            uvb = last.UpvalBindings(to_bind, new_name)
            cur.upval_bindings[new_name] = uvb
            nested.params.insert(0,
                last.TypedVar(last.PointerDecl(uvb.struct), '$up'))

          # Remove the declaration from the body of the current function,
          # replacing calls to it.
          cur.body.entries.remove(nested)  # TODO: prob unnecessary O(n)
          self.add_to_toplevel.append(nested)
          # TODO: this is probably wrong/too simple; at least need to have
          # something to deal with a local declared with the same name as a
          # function.
          self.parent.replace_ident_references(cur.body, old_name, new_name)
          cur.symtab[new_name] = last.SymTabEntry(
              _KEYWORDS['auto'], nested, is_declared_local=True, is_hoisted_function=True)
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
      self.insert_global_or_error(tl)

  def create_tuple_struct(self, field_types, node):
    c_name_field_types = [self.get_mangled_c_type(t) for t in field_types]
    members = [last.TypedVar(t, '_%d' % i) for i,t in enumerate(field_types)]
    name = '$Tuple$' + '$'.join(str(x) for x in c_name_field_types)
    if name in self.generated_structs:
      return
    struct = last.Struct(name, members)
    struct.omit_constructor = True
    self.generated_structs[name] = GeneratedStructInfo(node, struct)

  def create_range_structs(self):
    # TODO: i32 vs i64
    range_struct = self.create_struct('$Range', [
        last.TypedVar(_KEYWORDS['i32'], 'start'),
        last.TypedVar(_KEYWORDS['i32'], 'stop'),
        last.TypedVar(_KEYWORDS['i32'], 'step')
      ])

    self.create_struct('$RangeIter', [
      last.TypedVar(last.PointerDecl(range_struct), 'range'),
      last.TypedVar(_KEYWORDS['i32'], 'cur')])

  def create_struct(self, name, members, node=None, omit_constructor=True):
    struct = last.Struct(name, members)
    struct.omit_constructor = True
    self.generated_structs[name] = GeneratedStructInfo(None, struct)
    return struct

  class ResolveIdents:
    def __init__(self, parent):
      self.parent = parent
      assert self.parent.current_function is None

    def visit_FuncDef(self, func):
      assert not self.parent.current_function
      self.parent.current_function = func

    def resolve_ident(self, ident, rhs_type, tuple_index):
      found = rhs_type
      if tuple_index is not None:
        found = found.members[tuple_index].type
      x = self.parent.current_function.symtab.get(ident.name)
      assert x, "ident not in scope? '%s'" % ident.name
      if x.type is _KEYWORDS['auto']:
        x.type = found
      else:
        if x.type != found:
          if (isinstance(x.type, last.OptionalDecl) and
              (x.type.base is found or found is _KEYWORDS['null'])):
            # Allow coercion from contained type of optional to the optional,
            # or from null to any optional.
            pass
          else:
            self.parent.error_at(ident, 'previously typed as "%s", now "%s"' % (x.type, found))

    def visit_For(self, node):
      if isinstance(node.it, last.Ident):
        tuple_index = 0

      coll_type = self.parent.expr_type(self.parent.current_function, node.collection)
      if coll_type is _RANGE_TYPE:
        # HACK because literals are always i32 not i64, and no auto convert
        rhs_type = _KEYWORDS['i32']
      elif isinstance(coll_type, last.ListType):
        rhs_type = coll_type.base
      else:
        assert False, "todo %s" % coll_type
      self.resolve_ident(node.it, rhs_type, tuple_index=None)

    def visit_Assign(self, assign):
      if isinstance(assign.lhs, last.Ident):
        rhs_type = self.parent.expr_type(self.parent.current_function, assign.rhs)
        self.resolve_ident(assign.lhs, rhs_type, tuple_index=None)
      elif isinstance(assign.lhs, last.TupleAssign):
        assert all(isinstance(x, last.Ident) for x in assign.lhs.targets)
        rhs_type = self.parent.expr_type(self.parent.current_function, assign.rhs)
        for i,x in enumerate(assign.lhs.targets):
          self.resolve_ident(x, rhs_type, tuple_index=i)

    def visit_OptionalDecl(self, od):
      c_base_type_name = self.parent.get_mangled_c_type(od.base)
      if c_base_type_name not in self.parent.generated_structs:
        opt_struct_name = '$Opt$' + c_base_type_name
        members = [last.TypedVar(_KEYWORDS['bool'], 'has'),
                   last.TypedVar(od.base, 'val')]
        struct = last.Struct(opt_struct_name, members)
        struct.omit_constructor = True
        self.parent.generated_structs[c_base_type_name] = GeneratedStructInfo(od, struct)

    def visit_TupleCreate(self, tc):
      field_types = [self.parent.expr_type(self.parent.current_function, v) for v in tc.values]
      self.parent.create_tuple_struct(field_types, tc)

    def make_list_struct(self, elem_type, node):
      members = [
          last.TypedVar(last.PointerDecl(elem_type), "ptr"),
          last.TypedVar(_KEYWORDS['i64'], "len"),
          last.TypedVar(_KEYWORDS['i64'], "cap")
      ]
      base_type_name = self.parent.get_mangled_c_type(elem_type)
      name = '$List$' + base_type_name
      struct = last.Struct(name, members)
      struct.omit_constructor = True
      self.parent.generated_structs[base_type_name] = GeneratedStructInfo(node, struct)
      self.parent.HACK_generate_list_int32_methods = True

    def visit_ListComprehension(self, lc):
      elem_type = self.parent.expr_type(self.parent.current_function, lc.body.result)
      self.make_list_struct(elem_type, lc)

    def visit_List(self, l):
      if len(l.values) == 0:
        self.parent.error_at(l, "can't determine type of empty list yet")
      t = self.parent.expr_type(self.parent.current_function, l.values[0])
      for i in l.values[1:]:
        t2 = self.parent.expr_type(self.parent.current_function, i)
        if t is not t2:
          self.error_at(l, 'inconsistent types in list, was "%s" now "%s"' % (t, t2))
      self.make_list_struct(t, l)

    def visit_FuncCall(self, funccall):
      if isinstance(funccall.func, last.Ident):
        glob = self.parent.globals.get(funccall.func.name)
        if glob and isinstance(glob.ref_node, last.MacroDef):
          return self.parent.expand_macro(funccall, glob.ref_node)

    def after_FuncDef(self, func):
      assert self.parent.current_function == func
      for nested_name, uvb in func.upval_bindings.items():
        # Resolving references to upvals that were previously untyped
        # (|x| in test/run/nested_func_ref_up.luv)
        for ident, ste in uvb.to_bind.items():
          assert ste.is_upval and ste.func_ref_if_upval
          if ste.type is _KEYWORDS['auto']:
            ste.type = ste.func_ref_if_upval.symtab[ident].type

            # And also the members of the upval structure
            # (|y| in test/run/nested_func_ref_up_double.luv).
            for mem in uvb.struct.members:
              if mem.name == ident:
                mem.type = ste.type

      self.parent.current_function = None

    def visit_Struct(self, struct):
      pass

  def resolve_idents(self):
    resolver = self.ResolveIdents(self)
    self.Visit(resolver, self.ast_root)

  def expand_macro(self, node, mac):
    assert (isinstance(node, last.FuncCall) and isinstance(node.func, last.Ident)
            and isinstance(mac, last.MacroDef))
    #print("CALLING MACRO", node.func.name)
    class Macro:
      def __init__(s):
        s.args = node.args
        s.block = None
        s.func = self.current_function
        s._KEYWORDS = _KEYWORDS
      def parse_expr(s, code):
        tree = self.parser.parse(code + '\n')
        ast = ToAst().transform(tree)
        return ast.body.entries[0]
      def parse_toplevel(s, code):
        tree = self.parser.parse(code + '\n')
        ast = ToAst().transform(tree)
        return ast
    macro = Macro()
    result = mac.pyfunc(macro)
    #print('RETURING A THING')
    return result

  def find_return_stmts(self, func):
    class FindReturns:
      def __init__(self): self.result = []
      def visit_Return(self, node): self.result.append(node)
    finder = FindReturns()
    self.Visit(finder, func, do_not_cross_types=[last.FuncDef])
    return finder.result

  def tuple_struct_for_types(self, field_types):
    c_name_field_types = [self.get_c_type(t) for t in field_types]
    name = '$Tuple$' + '$'.join(str(x) for x in c_name_field_types)
    self.create_tuple_struct(field_types, None)
    return self.generated_structs[name].struct

  def tuple_struct_for_values(self, func, values):
    field_types = [self.expr_type(func, v) for v in values]
    return self.tuple_struct_for_types(field_types)

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
    elif isinstance(expr, last.FuncCall):
      if isinstance(expr.func, last.Ident):
        if expr.func.name == 'range':
          return _RANGE_TYPE

        if expr.func.name == 'iter':
          assert len(expr.args) == 1
          arg_type = self.expr_type(funcdef, expr.args[0])
          return last.IterType(_RANGE_TYPE)

        if expr.func.name == 'next':
          assert len(expr.args) == 1
          arg_type = self.expr_type(funcdef, expr.args[0])
          assert isinstance(arg_type, last.IterType)
          if arg_type.base is _RANGE_TYPE:
            value_type = _KEYWORDS['i32']
          else:
            assert False, "todo"
          return self.tuple_struct_for_types([_KEYWORDS['bool'], value_type])

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
    elif isinstance(expr, last.UnaryExpr):
      rhs_type = self.expr_type(funcdef, expr.obj)
      if expr.op.name == '*':
        if not isinstance(rhs_type, last.PointerDecl):
          self.error_at(expr.obj, 'expecting pointer type for dereference')
        return rhs_type.base
      else:
        assert False, "unhandled unary op %s" % op
    elif isinstance(expr, last.Ident):
      if ste := funcdef.symtab.get(expr.name):
        return ste.type
      assert False, "unhandled Ident expr_type %s" % expr
    elif isinstance(expr, last.Expr):
      t0 = self.expr_type(funcdef, expr.chain[0])
      if t0 is None: return None  # HACK for recursive expr_type, see also in FuncCall.
      for i in range(1, len(expr.chain), 2):
        if (expr.chain[i].name not in ('+', '*', '-', '/') or
            self.expr_type(funcdef, expr.chain[i+1]) is not t0):
          break
      else:
        return t0
    elif isinstance(expr, last.ListComprehension):
      return last.ListType(self.expr_type(funcdef, expr.body.result))
    elif isinstance(expr, last.List):
      # Initial visit to create struct does other error checks.
      return last.ListType(self.expr_type(funcdef, expr.values[0]))
    elif isinstance(expr, last.GetAttr):
      lhs = self.expr_type(funcdef, expr.lhs)
      assert isinstance(lhs, last.Type)
      cur = lhs.base
      while isinstance(cur, last.PointerDecl):
        cur = cur.base
      assert isinstance(cur, last.Struct)
      for x in cur.members:
        if x.name == expr.rhs:
          return x.type
      else:
        assert '%s not found on %s' % (expr.rhs, cur)
    elif isinstance(expr, last.GetItem):
      obj = self.expr_type(funcdef, expr.obj)
      assert isinstance(obj, last.Type)
      return obj.base
    elif isinstance(expr, last.TupleCreate):
      return self.tuple_struct_for_values(funcdef, expr.values)
    elif isinstance(expr, last.TupleAssign):
      return '/*TUPLE ASSIGN TYPE*/'
    assert False, "unhandled expr_type %s" % expr

  def resolve_function_return_type(self, fd):
    if getattr(fd, 'resolving_return_type', None):
      return False
    setattr(fd, 'resolving_return_type', True)
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
          self.error_at(fd, 'couldn\'t resolve return type for "%s"' % fd.name)

  def infer_types(self):
    self.determine_all_auto_function_returns()

  def get_c_type(self, node):
    assert node is not _KEYWORDS['auto']
    if node == _KEYWORDS['i32']:
      return 'int32_t'
    if node == _KEYWORDS['u32']:
      return 'uint32_t'
    if node == _KEYWORDS['i64']:
      return 'int64_t'
    if node == _KEYWORDS['u64']:
      return 'uint64_t'
    if node == _KEYWORDS['bool']:
      return '_Bool'
    if node == _KEYWORDS['void']:
      return 'void'
    if node == _KEYWORDS['f32']:
      return 'float'
    if node == _KEYWORDS['str']:
      return 'struct $Str'
    if isinstance(node, last.RangeType):
      return 'struct $Range'
    if isinstance(node, last.IterType):
      return '%sIter' % self.get_c_type(node.base)
    if isinstance(node, last.PointerDecl):
      return self.get_c_type(node.base) + '*'
    if isinstance(node, last.OptionalDecl):
      return 'struct ' + self.generated_structs[self.get_mangled_c_type(node.base)].struct.name
    if isinstance(node, last.Struct):
      return 'struct ' + node.name
    if isinstance(node, last.ListType):
      return 'struct ' + self.generated_structs[self.get_mangled_c_type(node.base)].struct.name
    if isinstance(node, last.Type):
      return self.get_c_type(node.base)
    print('GET_C_TYPE', node)
    return '??/*%s*/' % node

  def get_mangled_c_type(self, node):
    x = self.get_c_type(node)
    x = x.replace('struct ', '')
    x = x.replace('* ', 'STAR')
    return x

  def get_safe_c_name(self, luv_name):
    # TODO
    return luv_name

  def expr(self, node):
    if isinstance(node, last.Ident):
      ste = self.current_function.symtab.get(node.name) if self.current_function else None
      if ste and ste.is_upval:
        return '*$up->%s' % self.get_safe_c_name(node.name)
      else:
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
      return self.expr(node.lhs) + '.' + node.rhs
    elif isinstance(node, last.GetItem):
      ty = self.expr_type(self.current_function, node.obj)
      c_type = self.get_mangled_c_type(ty)
      return '%s$__getitem__(&%s, %s)' % (c_type, self.expr(node.obj), self.expr(node.index))
    elif isinstance(node, last.FuncCall):
      if isinstance(node.func, last.Ident) and node.func.name == 'range':
        if len(node.args) == 1:
          return '(struct $Range){0,%s,1}' % self.expr(node.args[0])
        elif len(node.args) == 2:
          return '(struct $Range){%s,%s,1}' % (
              self.expr(node.args[0]), self.expr(node.args[1]))
        elif len(node.args) == 3:
          return '(struct $Range){%s,%s,%s}' % (
              self.expr(node.args[0]), self.expr(node.args[1]), self.expr(node.args[2]))
        else:
          self.error_at(node.func, 'incorrect number of arguments to "range"')

      if isinstance(node.func, last.Ident) and node.func.name == 'iter':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return '%s$__iter__(&%s)' % (self.get_mangled_c_type(arg_type), self.expr(node.args[0]))
        else:
          self.error_at(node.func, 'incorrect number of arguments to "iter"')

      if isinstance(node.func, last.Ident) and node.func.name == 'next':
        if len(node.args) == 1:
          arg_type = self.expr_type(self.current_function, node.args[0])
          return '%s$__next__(&%s)' % (self.get_mangled_c_type(arg_type), self.expr(node.args[0]))
        else:
          self.error_at(node.func, 'incorrect number of arguments to "next"')

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
        # TODO: probably expr_type and then c_type of that.
        iter_type = '%sIter' % thing_mangled_c_type
        result += 'struct %s %s = %s$__iter__(&%s);' % (
            iter_type, iter_tmp, thing_mangled_c_type, thing_tmp)

        assert isinstance(f.its, last.Ident), "todo"
        it_name = f.its.name
        result += '%sIterReturn %s = {0};' % (thing_mangled_c_type, it_ret_tmp)
        result += 'for(;;) {'
        result += '%s = %sIter$__next__(&%s);' % (it_ret_tmp, thing_mangled_c_type, iter_tmp)
        result += 'if (!(%s._0)) break;' % it_ret_tmp
        result += '%sIterValue %s = %s._1;' % (thing_mangled_c_type, it_name, it_ret_tmp)

        result += '%s$append(&%s, %s);' % (
            result_mangled_c_type, result_tmp, self.expr(node.body.result))
        result += '}'

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
          error_at(cur_op, 'can\'t "%s" with lhs=%s, rhs=%s' % (cur_op, l_type, r_type))
        c_type = self.get_c_type(l_type)
        tmp = get_tmp_var()
        tmp_ident = last.Ident(tmp)
        self.current_function.symtab[tmp] = last.SymTabEntry(
            l_type, cur_op, is_compiler_temporary=True)
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
    elif isinstance(node, last.TupleCreate):
      struct = self.tuple_struct_for_values(self.current_function, node.values)
      return '(struct %s){' % struct.name + ','.join(self.expr(v) for v in node.values) + '}'
    elif isinstance(node, last.TupleAssign):
      return '/*TupleAssign, should be handled in stmt() Assign?*/'
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
            self.get_c_type(opttype.base), node.cond.bind, self.expr(node.cond.optexpr))
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
      result += '%sIter %s = %s$__iter__(&%s);' % (
          coll_c_type, iter_tmp, coll_mangled_c_type, coll_tmp)
      assert isinstance(node.it, last.Ident), "todo"
      it_name = node.it.name
      result += '%sIterReturn %s = {0};' % (coll_mangled_c_type, it_ret_tmp)
      result += 'for(;;) {'
      result += '%s = %sIter$__next__(&%s);' % (it_ret_tmp, coll_mangled_c_type, iter_tmp)
      result += 'if (!(%s._0)) break;' % it_ret_tmp
      result += '%sIterValue %s = %s._1;' % (coll_mangled_c_type, it_name, it_ret_tmp)
      result += self.stmt(node.body)
      result += '}'
      return result
    elif isinstance(node, last.Return):
      result = 'return'
      if node.value:
        result += ' ' + self.expr(node.value)
      result += ';'
      return result
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
      if isinstance(node.lhs, last.TupleAssign):
        assert all(isinstance(x, last.Ident) for x in node.lhs.targets)
        rhs_type = self.expr_type(self.current_function, node.rhs)
        field_types = [x.type for x in rhs_type.members]
        struct = self.tuple_struct_for_types(field_types)
        tmp = get_tmp_var()
        result = 'struct %s %s = %s;\n' % (struct.name, tmp, self.expr(node.rhs))
        for i, x in enumerate(node.lhs.targets):
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
    elif isinstance(node, last.Nonlocal):
      return '/* NONLOCAL %s */;' % ', '.join(node.vars)
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
    for n, ste in func.symtab.items():
      if ste.is_declared_local and not ste.is_hoisted_function:
        if ste.type is _KEYWORDS['void']:
          self.error_at(ste.ref_node, 'can\'t declare local of type "%s"' % ste.type.base)
        result += '%(type)s %(name)s = (%(type)s){0};' % {
            'type': self.get_c_type(ste.type), 'name': self.get_safe_c_name(n)}
    for n, upval in func.upval_bindings.items():
      result += 'struct %s %s = {' % (upval.struct_name, upval.parent_binding_name)
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
    # TODO: probably homogenize this with user structs.
    for n, uvb in obj.upval_bindings.items():
      result += 'struct %s {' % uvb.struct_name
      for name, uv in uvb.to_bind.items():
        result += '%s* %s;' % (self.get_c_type(uv.type), self.get_safe_c_name(name))
      result += '};\n'
    return result

  def generate_struct(self, obj):
    assert isinstance(obj, last.Struct)
    result = '\nstruct %s {\n' % obj.name
    for field in obj.members:
      result += '%s %s;\n' % (self.get_c_type(field.type), self.get_safe_c_name(field.name))
    result += '};\n'
    return result

  def generate_struct_constructor(self, obj):
    assert isinstance(obj, last.Struct)
    if obj.omit_constructor:
      return ''
    result = '\nstruct %s %s(' % (obj.name, obj.name)
    for i,field in enumerate(obj.members):
      result += '%s %s' % (self.get_c_type(field.type), self.get_safe_c_name(field.name))
      if i < len(obj.members) - 1:
        result += ','
    result += '){\n'
    result += 'struct %s $_ = {0};\n' % obj.name
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
        self.error_at(n, 'recursive struct definition for "%s"' % n.name)
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
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
struct $Str {
  char* ptr;
  int64_t len;
};

#define $Str$__lit__(s) (struct $Str){s, sizeof(s) - 1}

struct $Str $Str$from_n(char* data, size_t len) {
  struct $Str s = {malloc(len + 1), len};
  memcpy(s.ptr, data, len + 1);
  return s;
}
struct $Str $Str$__add__(struct $Str a, struct $Str b) {
  char* p = malloc(a.len + b.len + 1);
  memcpy(p, a.ptr, a.len);
  memcpy(p + a.len, b.ptr, b.len + 1);
  return (struct $Str){p, a.len + b.len};
}
void $Str$__del__(struct $Str* self) {
  free(self->ptr);
}

#define double$__lit__(a) (a)
#define double$__del__(a)

#define int32_t$__lit__(a) (a)
#define int32_t$__del__(a)
#define int32_t$__add__(a, b) ((a)+(b))
#define int32_t$__sub__(a, b) ((a)-(b))
#define int32_t$__mul__(a, b) ((a)*(b))
#define int32_t$__div__(a, b) ((a)/(b))

static void printint(int x) {
  printf("%d\n", x);
}
static void printbool(_Bool x) {
  printf(x ? "true\n" : "false\n");
}
static void printstr(struct $Str s) {
  printf("%s\n", s.ptr);
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

      header('late implementations')
      f.write(r'''
// TODO: generate all this
#define $RangeIterReturn struct $Tuple$_Bool$int32_t
#define $RangeIterValue int32_t

struct $List$int32_tIter {
  struct $List$int32_t* seq;
  int32_t cur;
};

#define $List$int32_tIterReturn struct $Tuple$_Bool$int32_t
#define $List$int32_tIterValue int32_t

struct $RangeIter $Range$__iter__(struct $Range* self) {
  return (struct $RangeIter){self, self->start};
}

struct $Tuple$_Bool$int32_t $RangeIter$__next__(struct $RangeIter* iter) {
  if (iter->cur >= iter->range->stop) {
    return (struct $Tuple$_Bool$int32_t){0};
  }
  int32_t ret = iter->cur;
  iter->cur += iter->range->step;
  return (struct $Tuple$_Bool$int32_t){1, ret};
}
''')

      if self.HACK_generate_list_int32_methods:
        f.write(r'''
int32_t $List$int32_t$__getitem__(struct $List$int32_t* L, int64_t at) {
  assert(at >= 0 && at < L->len);
  return L->ptr[at];
}

struct $List$int32_tIter $List$int32_t$__iter__(struct $List$int32_t* self) {
  return (struct $List$int32_tIter){self, 0};
}

struct $Tuple$_Bool$int32_t $List$int32_tIter$__next__(struct $List$int32_tIter* iter) {
  if (iter->cur >= iter->seq->len) {
    return (struct $Tuple$_Bool$int32_t){0};
  }
  int32_t ret = iter->seq->ptr[iter->cur];
  iter->cur++;
  return (struct $Tuple$_Bool$int32_t){1, ret};
}

void $List$int32_t$__del__(struct $List$int32_t* L) {
  free(L->ptr);
  L->ptr = NULL;
  L->len = 0;
  L->cap = 0;
}

void $List$int32_t$reserve(struct $List$int32_t* L, int64_t cap) {
  if (L->cap < cap) {
    int32_t* newp = malloc(sizeof(int32_t) * cap);
    memcpy(newp, L->ptr, sizeof(int32_t) * L->len);
    // memset rest?
    free(L->ptr);
    L->ptr = newp;
    L->cap = cap;
  }
}

void $List$int32_t$append(struct $List$int32_t* L, int32_t value) {
  if (L->len == L->cap) {
    $List$int32_t$reserve(L, L->cap < 16 ? 16 : L->cap * 2);
  }
  L->ptr[L->len++] = value;
}
''')

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
  parser = Parser()

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
    c = Compiler(sys.argv[1], ast, parser)
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
