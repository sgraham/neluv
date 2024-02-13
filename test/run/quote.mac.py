def List(macro):
    assert len(macro.args) == 1
    name = macro.args[0].name
    c = 'List$' + name
    if not macro.have_global(c):
        ast = macro.quotes.QuotedList.unquote({
            '`C': last.Ident(c),
            '`T': last.Ident(name),
            '`I': last.Ident('ListIter$' + name)
            })
        macro.insert_global(ast)
    return macro.parse_expr(c)
