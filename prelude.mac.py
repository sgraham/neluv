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