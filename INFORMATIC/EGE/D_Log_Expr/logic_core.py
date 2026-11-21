"""Ядро логического конструктора: формулы-деревья, вычисление, эквивалентность, прямая.

Перенесено из `tests/didactics.py` (строки 15-180 и 630-761) без изменения поведения.

Формула -- вложенный кортеж. Листья: ("in","P") -- «x ∈ P», ("var","x") -- целое,
("c",n) -- число, ("tf",True/False) -- логическая константа. Узел -- имя операции
из OPS (см. TYPE, INFIX) плюс операнды.

Публичные имена: register_op, ev, show, size, subterms, replace, negate, not_run,
leaves, envs, counterexample, equiv, Line, evaluate, solve, verify, all_matter.

Только stdlib, от других модулей пакета не зависит.
"""
import copy
from itertools import product

INF = float("inf")
NB = 5                          # битовая область: числа 0..31
MASK = (1 << NB) - 1
MAX_SIZE = 28                   # максимум узлов в формуле
MAX_NOT_RUN = 2                 # не больше двух отрицаний подряд: ¬¬a можно, ¬¬¬a нет
LINE_NAMES = ("P", "Q", "R", "S")


# ============================================================ операции и узлы
# Листья: ("in","P") - логическая "x ∈ P"; ("var","x") - целое; ("c",n) - число;
#         ("tf",True/False) - логическая константа 1/0.
LEAF = ("in", "var", "c", "tf")
OPS = {"not": lambda a: not a, "nz": lambda a: a != 0, "bnot": lambda a: a ^ MASK}
TYPE = {"in": "bool", "var": "int", "c": "int", "tf": "bool",
        "not": "bool", "nz": "bool", "bnot": "int"}
INFIX, COMM, ASSOC, SETNAME = {}, set(), set(), {}
T, F = ("tf", True), ("tf", False)


def register_op(name, fn, sym, vtype, comm=False, assoc=False, setname=None):
    """Новая бинарная операция. vtype: 'bool' или 'int'.
    setname - как назвать её действие на множествах прямой (для логических операций)."""
    OPS[name], TYPE[name], INFIX[name] = fn, vtype, sym
    if comm:
        COMM.add(name)
    if assoc:
        ASSOC.add(name)
    if setname:
        SETNAME[name] = setname


register_op("and", lambda a, b: a and b, "∧", "bool", True, True, "пересечение (∧)")
register_op("or", lambda a, b: a or b, "∨", "bool", True, True, "объединение (∨)")
register_op("imp", lambda a, b: (not a) or b, "→", "bool",
            setname="a → b = (дополнение a) ∪ b")
register_op("eqv", lambda a, b: a == b, "≡", "bool", comm=True,
            setname="a ≡ b = (a ∩ b) ∪ (дополнения)")
register_op("band", lambda a, b: a & b, "&", "int", True, True)
register_op("bor", lambda a, b: a | b, "|", "int", True, True)
register_op("bxor", lambda a, b: a ^ b, "^", "int", True, True)


def is_bool(f):
    return TYPE.get(f[0]) == "bool"


def ev(f, env):
    k = f[0]
    if k in ("in", "var"):
        return env[f[1]]
    if k in ("c", "tf"):
        return f[1]
    return OPS[k](*[ev(c, env) for c in f[1:]])


def wrap(c):
    return show(c) if c[0] in ("var", "c", "tf") else "(" + show(c) + ")"


def cmp0(e):
    s = show(e)
    simple = e[0] in ("var", "c") or (e[0] == "band" and e[1][0] in ("var", "c")
                                      and e[2][0] in ("var", "c"))
    return s if simple else "(" + s + ")"


def show(f):
    k = f[0]
    if k == "in":
        return f"x ∈ {f[1]}"
    if k == "var":
        return f[1]
    if k == "c":
        return str(f[1])
    if k == "tf":
        return "1" if f[1] else "0"
    if k == "nz":
        return cmp0(f[1]) + " ≠ 0"
    if k == "bnot":
        return "~" + wrap(f[1])
    if k == "not":
        b = f[1]
        if b[0] == "in":
            return f"x ∉ {b[1]}"
        if b[0] == "nz":
            return cmp0(b[1]) + " = 0"
        return "¬" + wrap(b)
    if k in INFIX:
        return f"{wrap(f[1])} {INFIX[k]} {wrap(f[2])}"
    return str(f)


TEX_INFIX = {"and": r"\land", "or": r"\lor", "imp": r"\to", "eqv": r"\equiv",
             "band": r"\mathbin{\&}", "bor": r"\mathbin{|}", "bxor": r"\oplus"}


def wrap_tex(c):
    return show_tex(c) if c[0] in ("var", "c", "tf") else "(" + show_tex(c) + ")"


def cmp0_tex(e):
    s = show_tex(e)
    simple = e[0] in ("var", "c") or (e[0] == "band" and e[1][0] in ("var", "c")
                                      and e[2][0] in ("var", "c"))
    return s if simple else "(" + s + ")"


def show_tex(f):
    r"""Та же формула, что show(), но в LaTeX; $...$ ставит вызывающий.

    Отличия от show(): bnot -- \overline{...} (фигурные скобки сами группируют
    вложенное выражение, поэтому внешние круглые скобки не нужны) и конъюнкция
    битов -- \mathbin{\&}. Для операции, зарегистрированной через register_op
    без записи в TEX_INFIX, возвращается str(f) -- как и в show().
    """
    k = f[0]
    if k == "in":
        return r"x \in " + f[1]
    if k == "var":
        return f[1]
    if k == "c":
        return str(f[1])
    if k == "tf":
        return "1" if f[1] else "0"
    if k == "nz":
        return cmp0_tex(f[1]) + r" \ne 0"
    if k == "bnot":
        return r"\overline{" + show_tex(f[1]) + "}"
    if k == "not":
        b = f[1]
        if b[0] == "in":
            return r"x \notin " + b[1]
        if b[0] == "nz":
            return cmp0_tex(b[1]) + " = 0"
        return r"\neg " + wrap_tex(b)
    if k in TEX_INFIX:
        return f"{wrap_tex(f[1])} {TEX_INFIX[k]} {wrap_tex(f[2])}"
    return str(f)


def size(f):
    return 1 if f[0] in LEAF else 1 + sum(size(c) for c in f[1:])


def subterms(f, path=()):
    yield path, f
    if f[0] not in LEAF:
        for i, c in enumerate(f[1:], 1):
            yield from subterms(c, path + (i,))


def replace(f, path, new):
    if not path:
        return new
    i = path[0]
    return f[:i] + (replace(f[i], path[1:], new),) + f[i + 1:]


def negate(f, nt="not"):
    """Отрицание со снятием двойного."""
    return f[1] if f[0] == nt else (nt, f)


def not_run(f):
    """Самая длинная цепочка подряд идущих отрицаний (¬¬¬a -> 3)."""
    best = 0

    def go(g, run, kind):
        nonlocal best
        if g[0] in ("not", "bnot"):
            run = run + 1 if kind == g[0] else 1
            kind = g[0]
        else:
            run, kind = 0, None
        best = max(best, run)
        if g[0] not in LEAF:
            for c in g[1:]:
                go(c, run, kind)
    go(f, 0, None)
    return best


# ============================================================ проверка эквивалентности
def leaves(f, acc=None):
    acc = set() if acc is None else acc
    if f[0] in ("in", "var"):
        acc.add((f[0], f[1]))
    elif f[0] not in ("c", "tf"):
        for c in f[1:]:
            leaves(c, acc)
    return acc


_ENVS = {}


def envs(ls):
    if ls not in _ENVS:
        doms = [(False, True) if kd == "in" else range(MASK + 1) for kd, _ in ls]
        _ENVS[ls] = [{n: v for (_, n), v in zip(ls, vals)} for vals in product(*doms)]
    return _ENVS[ls]


def counterexample(f, g):
    ls = tuple(sorted(leaves(f) | leaves(g)))
    for env in envs(ls):
        if ev(f, env) != ev(g, env):
            return env
    return None


def equiv(f, g):
    return counterexample(f, g) is None


def num(v):
    return "-∞" if v == -INF else "+∞" if v == INF else str(v)


class Line:
    """Прямая разбита на элементы: 0=(-∞;p0), 1={p0}, 2=(p0;p1), 3={p1}, ... (скобки точные)."""
    def __init__(self, ivs):
        self.ivs = ivs
        self.pts = sorted({e for lo, hi in ivs.values() for e in (lo, hi)})
        self.n = 2 * len(self.pts) + 1
        self.all = frozenset(range(self.n))
        self.atom = {}
        for name, (lo, hi) in ivs.items():
            i, j = self.pts.index(lo), self.pts.index(hi)
            self.atom[name] = frozenset(range(2 * i + 1, 2 * j + 2))

    def bounds(self, e):
        if e % 2:
            p = self.pts[(e - 1) // 2]
            return p, p
        k = e // 2
        return (self.pts[k - 1] if k > 0 else -INF,
                self.pts[k] if k < len(self.pts) else INF)

    def runs(self, S):
        out, cur = [], []
        for e in range(self.n):
            if e in S:
                cur.append(e)
            elif cur:
                out.append(cur)
                cur = []
        if cur:
            out.append(cur)
        return out

    def fmt(self, S):
        if not S:
            return "∅"
        parts = []
        for r in self.runs(S):
            a, b = r[0], r[-1]
            lo, hi = self.bounds(a)[0], self.bounds(b)[1]
            if a == b and a % 2:
                parts.append("{" + num(lo) + "}")
            else:
                parts.append(("[" if a % 2 else "(") + f"{num(lo)}; {num(hi)}" + ("]" if b % 2 else ")"))
        return " ∪ ".join(parts)


def evaluate(L, f, log=None):
    """Множество точек прямой, где логическая формула истинна. Шаги пишет в log.
    Любая зарегистрированная логическая операция работает автоматически (поэлементно)."""
    k = f[0]
    if k == "in":
        return L.atom[f[1]]
    if k == "tf":
        return L.all if f[1] else frozenset()
    if k == "not":
        r, how = L.all - evaluate(L, f[1], log), "дополнение до всей прямой (¬)"
    elif TYPE.get(k) == "bool" and k in INFIX:
        a, b = evaluate(L, f[1], log), evaluate(L, f[2], log)
        r = frozenset(e for e in range(L.n) if OPS[k](e in a, e in b))
        how = SETNAME.get(k, f"поэлементно по операции {INFIX[k]}")
    else:
        raise ValueError(f"узел {k} нельзя вычислить на прямой")
    if log is not None and all(x[0] != f for x in log):
        log.append((f, r, how))
    return r


def solve(L, I, O, want):
    """A обязан содержать I и не пересекать O. -> (ответ, строки, lo, hi) | None"""
    allowed = L.all - O
    if want == "min":
        if not I:
            return None
        a, b = min(I), max(I)
        if any(e in O for e in range(a, b + 1)):
            return None
        lo, hi = L.bounds(a)[0], L.bounds(b)[1]
        if lo == -INF or hi == INF or hi - lo <= 0:
            return None
        return hi - lo, [f"A должен содержать множество {L.fmt(I)}.",
                         f"Наименьший такой отрезок: от {lo} до {hi}, длина {hi} − {lo} = {hi - lo}."], lo, hi
    runs = L.runs(allowed)
    if I:
        run = next((r for r in runs if min(I) in r), None)
        if run is None or max(I) not in run:
            return None
    else:
        if not O or not runs:
            return None
        run = max(runs, key=lambda r: L.bounds(r[-1])[1] - L.bounds(r[0])[0])
    lo, hi = L.bounds(run[0])[0], L.bounds(run[-1])[1]
    if lo == -INF or hi == INF or hi - lo <= 0:
        return None
    lines = [f"A не может содержать точки множества {L.fmt(O)}, значит A лежит в {L.fmt(allowed)}."]
    if I:
        lines.append(f"A обязан содержать {L.fmt(I)}; это внутри промежутка {L.fmt(frozenset(run))}.")
    else:
        lines.append(f"Самый длинный промежуток: {L.fmt(frozenset(run))}.")
    lines.append(f"Наибольшая длина: {hi} − {lo} = {hi - lo}.")
    return hi - lo, lines, lo, hi


def verify(L, cond, lo, hi):
    """Независимая проверка ответа в контрольных точках.

    Точки: сами концы отрезков (L.pts), по одной точке вне прямой с каждой
    стороны и середины всех промежутков между концами -- именно на границах
    решается, входит точка в A или нет.
    """
    p = L.pts
    xs = [p[0] - 1, p[-1] + 1] + list(p) + [(a + b) / 2 for a, b in zip(p, p[1:])]
    for x in xs:
        env = {n: a <= x <= b for n, (a, b) in L.ivs.items()}
        env["A"] = lo <= x <= hi
        if not cond(env):
            return False
    return True


def all_matter(L, names, answer_fn):
    """Каждый отрезок из names должен влиять на ответ: если замена его на ∅ и на всю
    прямую не меняет ответ, отрезок лишний, и задача отбрасывается."""
    base = answer_fn(L)
    for n in names:
        same = 0
        for repl in (frozenset(), L.all):
            L2 = copy.copy(L)
            L2.atom = dict(L.atom)
            L2.atom[n] = repl
            same += answer_fn(L2) == base
        if same == 2:
            return False
    return True
