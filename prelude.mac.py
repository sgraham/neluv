import last

def instantiate_list(macro):
    pass

def range(macro):
    def buildit(a, b, c):
        return last.FuncCall(last.Ident('Range'), args=[a,b,c])

    if len(macro.args) == 1:
        return buildit(last.Number(0), macro.args[0], last.Number(1))
    elif len(macro.args) == 2:
        return buildit(macro.args[0], macro.args[1], last.Number(1))
    elif len(macro.args) == 3:
        return buildit(macro.args[0], macro.args[1], macro.args[2])
    else:
        assert False, "unexpected number of args to range()"

# Don't forget to use __builtins__['print'], etc. when debugging this function.
def print(macro):
    result = []
    for i,a in __builtins__['enumerate'](macro.args):
        ty = macro.expr_type(a)
        if ty is macro.keywords['i32']:
            result.append(last.FuncCall(last.Ident('printint'), [a]))
        elif ty is macro.keywords['bool']:
            result.append(last.FuncCall(last.Ident('printbool'), [a]))
        elif ty is macro.keywords['str']:
            result.append(last.FuncCall(last.Ident('printstr'), [a]))
        elif isinstance(ty, last.TupleDecl):
            result.append(last.FuncCall(last.Ident('printstr'), [last.String("<todo: tuple>")]))
        else:
            assert False, 'todo %s' % ty
        if i < len(macro.args) - 1:
            result.append(last.FuncCall(last.Ident('printspace'), []))
    result.append(last.FuncCall(last.Ident('printnl'), []))
    return last.Block(result)

def enumerate(macro):
    # XXX This needs some way to evaluate the return type of __iter__ of the
    # type of macro.args[0], and probably the return type of __next__ of that
    # type so that it can declare the correct struct types.
    assert False, "todo"
    assert len(macro.args) == 1
    ty = macro.expr_type(macro.args[0])
    e = 'Enumerator_' + macro.get_c_type(ty)
    if not macro.have_global(e):
        ast = macro.unquote(macro.quotes.QuotedEnumerate, {
            '`E': last.Ident(e),
            '`I': macro.keyword_or_ident(macro.get_c_type(ty))
        })
        import pprint
        pprint.pprint('UNQUOTE RESULT')
        pprint.pprint(ast)
        for tl in ast.body.entries:
            assert isinstance(tl.name, last.Ident), tl.name
            macro.insert_global(tl.name.name, tl)
    return last.FuncCall(
            macro.parse_expr(e),
            args=[last.FuncCall(last.Ident('iter'), [macro.args[0]]),
                  last.Number(0)])

def List(macro):
    assert len(macro.args) == 1
    assert isinstance(macro.args[0], last.Type)
    name = macro.args[0].base
    #__builtins__['print']('NAME', name)
    c = 'List_' + name
    if not macro.have_global(c):
        ast = macro.unquote(macro.quotes.QuotedList, {
            '`C': last.Ident(c),
            '`T': macro.keyword_or_ident(name),
            '`I': last.Ident('ListIter_' + name)
            })
        #import pprint
        #pprint.pprint('UNQUOTE RESULT')
        #pprint.pprint(ast)
        for tl in ast.body.entries:
            assert isinstance(tl.name, last.Ident), tl.name
            #print('INSERT', tl.name.name)
            macro.insert_global(tl.name.name, tl)
    return last.FuncCall(macro.parse_expr(c),
                         args=[macro.keyword_or_ident('null'), last.Number(0), last.Number(0)])
