import last
#import pprint

def FixedArray(macro):
    assert len(macro.args) == 2
    assert isinstance(macro.args[0], last.Type)
    name = macro.args[0].base
    assert isinstance(macro.args[1], last.Number)
    fixedcap = macro.args[1].value
    c = 'FixedArray_' + name
    if not macro.have_global(c):
        ast = macro.unquote(macro.quotes.FixedArrayQuoted, {
            '`C': last.Ident(c),
            '`T': macro.keyword_or_ident(name),
            '`I': last.Ident('FixedArrayIter_' + name),
            '`L': last.Number(fixedcap),
            })
        #pprint.pprint('UNQUOTE RESULT')
        #pprint.pprint(ast)
        for tl in ast.body.entries:
            assert isinstance(tl.name, last.Ident), tl.name
            #print('INSERT', tl.name.name)
            macro.insert_global(tl.name.name, tl)
    return last.FuncCall(macro.parse_expr(c),
                         args=[macro.keyword_or_ident('null'), last.Number(0)])
