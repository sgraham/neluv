import last

'''
struct List$T:
    *T ptr
    int len
    int cap

struct List$T_Iter:
    *List$T seq
    int cur

on List$T:
    def __getitem__(*List$T self, int at):
        // assert at >= 0 and at < self.len
        return self.ptr[at]

    def __iter__(*List$T self):
        return List$T_Iter(self, 0)

    def __del__(*List$T self):
        free(self.ptr)
        L.ptr = NULL
        L.len = 0
        L.cap = 0

    def reserve(*List$T self, int cap):
        if self.cap < cap:
            *int newp = malloc(sizeof(int) * cap)
            memcpy(newp, self.ptr, sizeof(int) * self.len)
            // memset rest?
            free(self.ptr)
            self.ptr = newp
            self.cap = cap

    def append(*List$T self, $T value):
        self.reserve(16 if self.cap < 16 else self.cap * 2)
        self.ptr[self.len] = value
        self.len += 1

on List$T_Iter:
    def __next__(*List$T_Iter self):
        if self.cur >= self.seq.len:
            return false, 0
        ret = self.seq.ptr[self.cur]
        self.cur += 1
        return true, ret
'''

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
        __builtins__['print'](ty)
        __builtins__['print'](ty is macro.keywords['i32'])
        if ty is macro.keywords['i32']:
            result.append(last.FuncCall(last.Ident('printint'), [a]))
        elif ty is macro.keywords['bool']:
            result.append(last.FuncCall(last.Ident('printbool'), [a]))
        elif ty is macro.keywords['str']:
            result.append(last.FuncCall(last.Ident('printstr'), [a]))
        else:
            assert False, 'todo %s' % ty
        if i < len(macro.args) - 1:
            result.append(last.FuncCall(last.Ident('printspace'), []))
    result.append(last.FuncCall(last.Ident('printnl'), []))
    return last.Block(result)
