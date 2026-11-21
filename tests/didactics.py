#!/usr/bin/env python3
"""Дедуктивный конструктор задач (логика + числовая прямая + битовые операции).

Формулы - деревья-кортежи. Теоремы (@rule) и операции (register_op) регистрируются
снаружи. Задача = простое ядро + цепочка проверенных преобразований; решение =
эта цепочка в обратную сторону + вычисление на прямой / переборе.
"""
import copy
import random
from collections import Counter, defaultdict
from dataclasses import dataclass
from functools import partial
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


# ============================================================ реестр правил (теорем)
TOPICS = {}                                    # тема -> [функции-правила]
STATS = defaultdict(lambda: [0, 0, 0, 0])      # применимо / принято / неверно / ошибка
BIT_ONLY = {"xor", "bit_test", "const_split", "bit_not"}   # темы, бессмысленные на прямой


def rule(topic):
    """Регистрирует правило: (узел, ctx) -> (новый_узел, 'название закона') | None."""
    def deco(fn):
        TOPICS.setdefault(topic, []).append(fn)
        return fn
    return deco


class Ctx:
    def __init__(self, rnd, lit, bitleaf=None):
        self.rnd, self.lit = rnd, lit            # lit() - случайный логический литерал
        self.bitleaf = bitleaf or (lambda: ("var", "x"))


# ---------------------------------------------------------------- логика
@rule("negation")
def r_dneg(f, ctx):
    if is_bool(f):
        if f[0] == "not":
            return None
        return ("not", ("not", f)), "двойное отрицание: ¬¬a ≡ a"
    if f[0] == "bnot":
        return None
    return ("bnot", ("bnot", f)), "двойное побитовое отрицание: ~~a = a"


def _morgan(f, ops, nt):
    dual = {ops[0]: ops[1], ops[1]: ops[0]}
    if f[0] in dual:
        return (nt, (dual[f[0]], negate(f[1], nt), negate(f[2], nt)))
    if f[0] == nt and f[1][0] in dual:
        g = f[1]
        return (dual[g[0]], negate(g[1], nt), negate(g[2], nt))
    return None


@rule("morgan")
def r_morgan_bool(f, ctx):
    r = _morgan(f, ("and", "or"), "not")
    return (r, "закон де Моргана: ¬(a ∧ b) ≡ ¬a ∨ ¬b, ¬(a ∨ b) ≡ ¬a ∧ ¬b") if r else None


@rule("morgan")
def r_morgan_bit(f, ctx):
    r = _morgan(f, ("band", "bor"), "bnot")
    return (r, "закон де Моргана для битов: ~(a & b) = ~a | ~b, ~(a | b) = ~a & ~b") if r else None


@rule("implication")
def r_imp(f, ctx):
    if f[0] == "imp":
        return ("or", negate(f[1]), f[2]), "импликация: a → b ≡ ¬a ∨ b"
    if f[0] == "or":
        return ("imp", negate(f[1]), f[2]), "импликация: ¬a ∨ b ≡ a → b"


@rule("implication")
def r_contra(f, ctx):
    if f[0] == "imp":
        return ("imp", negate(f[2]), negate(f[1])), "контрапозиция: a → b ≡ ¬b → ¬a"


@rule("implication")
def r_neg_imp(f, ctx):
    if f[0] == "not" and f[1][0] == "imp":
        return ("and", f[1][1], negate(f[1][2])), "отрицание импликации: ¬(a → b) ≡ a ∧ ¬b"
    if f[0] == "and":
        return ("not", ("imp", f[1], negate(f[2]))), "a ∧ b ≡ ¬(a → ¬b)"


@rule("exportation")
def r_export(f, ctx):
    if f[0] == "imp" and f[1][0] == "and":
        return ("imp", f[1][1], ("imp", f[1][2], f[2])), "экспортация: (a ∧ b) → c ≡ a → (b → c)"
    if f[0] == "imp" and f[2][0] == "imp":
        return ("imp", ("and", f[1], f[2][1]), f[2][2]), "экспортация: a → (b → c) ≡ (a ∧ b) → c"


@rule("impl_distr")
def r_imp_distr(f, ctx):
    if f[0] == "imp" and f[2][0] == "and":
        return ("and", ("imp", f[1], f[2][1]), ("imp", f[1], f[2][2])), \
            "a → (b ∧ c) ≡ (a → b) ∧ (a → c)"
    if f[0] == "imp" and f[1][0] == "or":
        return ("and", ("imp", f[1][1], f[2]), ("imp", f[1][2], f[2])), \
            "(a ∨ b) → c ≡ (a → c) ∧ (b → c)"
    if f[0] == "and" and f[1][0] == "imp" and f[2][0] == "imp":
        (a, b), (c, d) = f[1][1:], f[2][1:]
        if a == c:
            return ("imp", a, ("and", b, d)), "(a → b) ∧ (a → d) ≡ a → (b ∧ d)"
        if b == d:
            return ("imp", ("or", a, c), b), "(a → b) ∧ (c → b) ≡ (a ∨ c) → b"


@rule("equivalence")
def r_eqv(f, ctx):
    if f[0] != "eqv":
        return None
    a, b = f[1], f[2]
    if ctx.rnd.random() < 0.5:
        return ("and", ("imp", a, b), ("imp", b, a)), "a ≡ b равносильно (a → b) ∧ (b → a)"
    return ("or", ("and", a, b), ("and", negate(a), negate(b))), \
        "a ≡ b равносильно (a ∧ b) ∨ (¬a ∧ ¬b)"


@rule("equivalence")
def r_eqv_back(f, ctx):
    if f[0] == "or" and f[1][0] == "and" and f[2][0] == "and":
        a, b = f[1][1], f[1][2]
        if f[2][1] == negate(a) and f[2][2] == negate(b):
            return ("eqv", a, b), "(a ∧ b) ∨ (¬a ∧ ¬b) равносильно a ≡ b"


@rule("commutativity")
def r_comm(f, ctx):
    if f[0] in COMM:
        return (f[0], f[2], f[1]), "коммутативность: a ∘ b ≡ b ∘ a"


@rule("associativity")
def r_assoc(f, ctx):
    k = f[0]
    if k not in ASSOC:
        return None
    txt = "ассоциативность: (a ∘ b) ∘ c ≡ a ∘ (b ∘ c)"
    if f[1][0] == k:
        return (k, f[1][1], (k, f[1][2], f[2])), txt
    if f[2][0] == k:
        return (k, (k, f[1], f[2][1]), f[2][2]), txt


DIST = [("and", "or"), ("or", "and"), ("band", "bor"), ("bor", "band"), ("band", "bxor")]


@rule("distributivity")
def r_distr(f, ctx):
    opts, k = [], f[0]
    for kk, oo in DIST:
        if k == kk:
            a, b = f[1], f[2]
            if b[0] == oo:
                opts.append((oo, (kk, a, b[1]), (kk, a, b[2])))
            if a[0] == oo:
                opts.append((oo, (kk, a[1], b), (kk, a[2], b)))
        if k == oo:
            a, b = f[1], f[2]
            if a[0] == kk and b[0] == kk and a[1] == b[1]:
                opts.append((kk, a[1], (oo, a[2], b[2])))
    if opts:
        return ctx.rnd.choice(opts), \
            "дистрибутивность: a ∘ (b ∗ c) ≡ (a ∘ b) ∗ (a ∘ c) и вынесение за скобки"


@rule("idempotency")
def r_idem(f, ctx):
    if size(f) > 3:
        return None
    if is_bool(f):
        return (ctx.rnd.choice(("and", "or")), f, f), "идемпотентность: a ∧ a ≡ a, a ∨ a ≡ a"
    return (ctx.rnd.choice(("band", "bor")), f, f), "идемпотентность: a & a = a, a | a = a"


@rule("absorption")
def r_absorb(f, ctx):
    if size(f) > 3:
        return None
    if is_bool(f):
        k, o = ctx.rnd.choice((("or", "and"), ("and", "or")))
        extra, txt = ctx.lit(), "поглощение: a ∨ (a ∧ b) ≡ a, a ∧ (a ∨ b) ≡ a"
    else:
        k, o = ctx.rnd.choice((("bor", "band"), ("band", "bor")))
        extra, txt = ctx.bitleaf(), "поглощение: a | (a & b) = a, a & (a | b) = a"
    return (k, f, (o, f, extra)), txt


# ---------------------------------------------------------------- константы 0 и 1
@rule("constants")
def r_neutral(f, ctx):
    if not is_bool(f) or f[0] == "tf":
        return None
    if ctx.rnd.random() < 0.5:
        return ("or", f, F), "нейтральный элемент: a ∨ 0 ≡ a"
    return ("and", f, T), "нейтральный элемент: a ∧ 1 ≡ a"


@rule("constants")
def r_neutral_drop(f, ctx):
    if f[0] == "or" and F in (f[1], f[2]):
        return (f[2] if f[1] == F else f[1]), "нейтральный элемент: a ∨ 0 ≡ a"
    if f[0] == "and" and T in (f[1], f[2]):
        return (f[2] if f[1] == T else f[1]), "нейтральный элемент: a ∧ 1 ≡ a"


@rule("constants")
def r_absorbing(f, ctx):
    if f[0] == "or" and T in (f[1], f[2]):
        return T, "a ∨ 1 ≡ 1"
    if f[0] == "and" and F in (f[1], f[2]):
        return F, "a ∧ 0 ≡ 0"


@rule("constants")
def r_excluded_middle(f, ctx):
    if f == T:
        a = ctx.lit()
        return ("or", a, negate(a)), "закон исключённого третьего: a ∨ ¬a ≡ 1"
    if f == F:
        a = ctx.lit()
        return ("and", a, negate(a)), "закон противоречия: a ∧ ¬a ≡ 0"
    if f[0] == "or" and f[2] == negate(f[1]):
        return T, "закон исключённого третьего: a ∨ ¬a ≡ 1"
    if f[0] == "and" and f[2] == negate(f[1]):
        return F, "закон противоречия: a ∧ ¬a ≡ 0"


# ---------------------------------------------------------------- биты
@rule("xor")
def r_xor_def(f, ctx):
    if f[0] == "bxor":
        a, b = f[1], f[2]
        if ctx.rnd.random() < 0.5:
            return ("bor", ("band", a, negate(b, "bnot")), ("band", negate(a, "bnot"), b)), \
                "a ^ b = (a & ~b) | (~a & b)"
        return ("band", ("bor", a, b), ("bnot", ("band", a, b))), "a ^ b = (a | b) & ~(a & b)"
    if f[0] == "bor" and f[1][0] == "band" and f[2][0] == "band":
        a, nb, na, b = f[1][1], f[1][2], f[2][1], f[2][2]
        if nb == negate(b, "bnot") and na == negate(a, "bnot"):
            return ("bxor", a, b), "(a & ~b) | (~a & b) = a ^ b"


@rule("xor")
def r_xor_zero(f, ctx):
    if is_bool(f) or size(f) > 3:
        return None
    return ("bxor", f, ("c", 0)), "a ^ 0 = a"


@rule("xor")
def r_xor_twice(f, ctx):
    if is_bool(f):
        return None
    k = ctx.bitleaf()
    return ("bxor", ("bxor", f, k), k), "(a ^ k) ^ k = a"


@rule("bit_not")
def r_bnot_xor(f, ctx):
    if f[0] == "bnot":
        return ("bxor", f[1], ("c", MASK)), f"~a = a ^ {MASK}  (в {NB} битах)"
    if f[0] == "bxor" and f[2] == ("c", MASK):
        return ("bnot", f[1]), f"a ^ {MASK} = ~a  (в {NB} битах)"


@rule("bit_test")
def r_nz_or(f, ctx):
    if f[0] == "nz" and f[1][0] == "bor":
        return ("or", ("nz", f[1][1]), ("nz", f[1][2])), "(a | b) ≠ 0 ⇔ (a ≠ 0) ∨ (b ≠ 0)"
    if f[0] == "or" and f[1][0] == "nz" and f[2][0] == "nz":
        return ("nz", ("bor", f[1][1], f[2][1])), "(a ≠ 0) ∨ (b ≠ 0) ⇔ (a | b) ≠ 0"
    if f[0] == "not" and f[1][0] == "nz" and f[1][1][0] == "bor":
        a, b = f[1][1][1], f[1][1][2]
        return ("and", ("not", ("nz", a)), ("not", ("nz", b))), "(a | b) = 0 ⇔ (a = 0) ∧ (b = 0)"
    if (f[0] == "and" and f[1][0] == "not" and f[2][0] == "not"
            and f[1][1][0] == "nz" and f[2][1][0] == "nz"):
        return ("not", ("nz", ("bor", f[1][1][1], f[2][1][1]))), "(a = 0) ∧ (b = 0) ⇔ (a | b) = 0"


def _bits(n):
    return [b for b in range(NB) if n >> b & 1]


@rule("const_split")
def r_const_or(f, ctx):
    if f[0] != "c":
        return None
    bs = _bits(f[1])
    if len(bs) < 2:
        return None
    part = ctx.rnd.sample(bs, ctx.rnd.randint(1, len(bs) - 1))
    n1 = sum(1 << b for b in part)
    return ("bor", ("c", n1), ("c", f[1] ^ n1)), f"разбиение битов числа: {f[1]} = {n1} | {f[1] ^ n1}"


@rule("const_split")
def r_const_xor(f, ctx):
    if f[0] != "c":
        return None
    n1 = ctx.rnd.randint(1, MASK)
    return ("bxor", ("c", n1), ("c", f[1] ^ n1)), f"{f[1]} = {n1} ^ {f[1] ^ n1}"


@rule("const_split")
def r_const_and(f, ctx):
    if f[0] != "c":
        return None
    free = [b for b in range(NB) if not f[1] >> b & 1]
    if not free:
        return None
    e1 = e2 = 0
    for b in free:
        c = ctx.rnd.choice((0, 1, 2))
        if c == 1:
            e1 |= 1 << b
        elif c == 2:
            e2 |= 1 << b
    n1, n2 = f[1] | e1, f[1] | e2
    return ("band", ("c", n1), ("c", n2)), f"{f[1]} = {n1} & {n2}"


# ============================================================ цепочка преобразований
def apply_topic(cur, topic, ctx, seen):
    rules = TOPICS[topic][:]
    ctx.rnd.shuffle(rules)
    positions = list(subterms(cur))
    ctx.rnd.shuffle(positions)
    for fn in rules:
        st = STATS[fn.__name__]
        for path, node in positions:
            try:
                res = fn(node, ctx)
            except Exception:
                st[3] += 1
                continue
            if res is None:
                continue
            new = replace(cur, path, res[0])
            st[0] += 1
            if new in seen or size(new) > MAX_SIZE or not_run(new) > MAX_NOT_RUN:
                continue
            if not equiv(cur, new):          # главная защита: неверный «закон» не пройдёт
                st[2] += 1
                continue
            st[1] += 1
            return new, res[1]
    return None


def obfuscate(f, schedule, ctx):
    """По одному закону на каждую тему из schedule. Тема, которой пока негде сработать,
    откладывается в конец очереди. -> ((формула, история), None) | (None, причина)"""
    cur, seen, hist = f, {f}, []
    queue, stuck = list(schedule), 0
    while queue:
        topic = queue.pop(0)
        res = apply_topic(cur, topic, ctx, seen)
        if res is None:
            queue.append(topic)
            stuck += 1
            if stuck >= len(queue):
                return None, f"тема «{topic}» не нашла, где сработать"
            continue
        new, law = res
        hist.append((law, cur, new))
        seen.add(new)
        cur, stuck = new, 0
    return (cur, hist), None


def rule_report():
    print(f"{'правило':<18}{'применимо':>10}{'принято':>9}{'неверно':>9}{'ошибок':>8}")
    for name, (a, b, c, d) in sorted(STATS.items()):
        print(f"{name:<18}{a:>10}{b:>9}{c:>9}{d:>8}")


# ============================================================ случайные формулы
def line_lit(rnd, names):
    v = ("in", rnd.choice(names))
    return v if rnd.random() < 0.55 else ("not", v)


def bit_lit(rnd):
    v = ("nz", ("band", ("var", "x"), ("c", rnd.randint(1, MASK))))
    return v if rnd.random() < 0.5 else ("not", v)


def bit_leaf(rnd):
    return ("var", "x") if rnd.random() < 0.6 else ("c", rnd.randint(1, MASK))


def rand_bits(rnd, d):
    if d == 0:
        return bit_leaf(rnd)
    op = rnd.choice(("band", "bor", "bxor", "bnot"))
    if op == "bnot":
        return ("bnot", rand_bits(rnd, d - 1))
    return (op, rand_bits(rnd, d - 1), rand_bits(rnd, rnd.choice((0, d - 1))))


def rand_h(lit, rnd, depth):
    def gen(d):
        if d == 0:
            return lit()
        op = rnd.choice(("and", "or", "imp", "eqv", "or", "imp"))
        return (op, gen(rnd.choice((0, d - 1))), gen(rnd.choice((0, d - 1))))
    for _ in range(40):
        f = gen(depth)
        if len({n for _, n in subterms(f) if n[0] in ("in", "nz")}) >= 2:
            break
    return f


def probe_rule(fn, n=300, seed=0):
    """Проверка гипотезы: как часто правило применимо и верно ли оно."""
    rnd = random.Random(seed)
    c_line = Ctx(rnd, lambda: line_lit(rnd, ("P", "Q", "R")))
    c_bit = Ctx(rnd, lambda: bit_lit(rnd), lambda: bit_leaf(rnd))

    def nz_lit():
        v = ("nz", rand_bits(rnd, 2))
        return v if rnd.random() < 0.5 else ("not", v)
    pops = [(c_line, lambda: rand_h(c_line.lit, rnd, 2)),
            (c_bit, lambda: rand_h(c_bit.lit, rnd, 2)),
            (c_bit, lambda: rand_h(nz_lit, rnd, 2)),
            (c_bit, lambda: rand_bits(rnd, 3))]
    tried = ok = bad = err = 0
    example = None
    for _ in range(n):
        ctx, make = rnd.choice(pops)
        for _, node in subterms(make()):
            try:
                res = fn(node, ctx)
            except Exception:
                err += 1
                continue
            if res is None:
                continue
            tried += 1
            cex = counterexample(node, res[0])
            if cex is None:
                ok += 1
            else:
                bad += 1
                example = example or (node, res[0], cex)
    print(f"{fn.__name__}: применимо {tried}, верно {ok}, НЕВЕРНО {bad}, ошибок {err}")
    if tried == 0:
        print("  правило ни разу не нашло, где сработать")
    if example:
        a, b, env = example
        print(f"  контрпример: {show(a)}   и   {show(b)}   различаются при {env}")


# ============================================================ числовая прямая
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
    """Независимая проверка ответа в контрольных точках (лучи и середины промежутков)."""
    p = L.pts
    xs = [p[0] - 1, p[-1] + 1] + [(a + b) / 2 for a, b in zip(p, p[1:])]
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


# ============================================================ параметры и задачи
@dataclass
class TaskParams:
    kinds: tuple = None             # None = все виды из KINDS
    topics: tuple = None            # None = все подходящие теме задачи (см. default_topics)
    steps: object = (2, 4)          # число преобразований: int или (мин, макс)
    n_intervals: int = 3            # 2..4 отрезка для задач на прямой
    each_topic: bool = True         # каждая выбранная тема встретится хотя бы раз
    unique_skeleton: bool = True    # не повторять одинаковую последовательность законов


@dataclass
class Task:
    number: int
    kind: str
    text: str
    answer: int
    solution: list
    steps: int
    topics: list
    skeleton: tuple

    def statement(self):
        return f"Задача {self.number}. {self.text}"

    def solution_text(self):
        head = (f"Решение задачи {self.number} (преобразований: {self.steps}; "
                f"темы: {', '.join(self.topics) or '—'})")
        return head + "\n" + "\n".join(self.solution) + f"\nОтвет: {self.answer}"


def default_topics(kind):
    ts = list(TOPICS)
    return ts if kind.startswith("bit") else [t for t in ts if t not in BIT_ONLY]


def pick_schedule(rnd, p, kind):
    lo, hi = (p.steps, p.steps) if isinstance(p.steps, int) else p.steps
    steps = rnd.randint(lo, hi)
    topics = list(p.topics or default_topics(kind))
    if p.each_topic:
        sched = (rnd.sample(topics, steps) if steps <= len(topics)
                 else topics + [rnd.choice(topics) for _ in range(steps - len(topics))])
    else:
        sched = [rnd.choice(topics) for _ in range(steps)]
    rnd.shuffle(sched)
    return steps, sched


def chain_lines(final, hist):
    lines = [f"   {show(final)}"]
    for law, before, _ in reversed(hist):
        lines.append(f" ≡ {show(before)}   [{law}]")
    return lines


# ---------------------------------------------------------------- виды 1-3: отрезок A на прямой
def rand_intervals(rnd, names, span=60):
    pts = rnd.sample(range(1, span + 1), 2 * len(names))
    return {n: (min(pts[2 * i], pts[2 * i + 1]), max(pts[2 * i], pts[2 * i + 1]))
            for i, n in enumerate(names)}


REASON = {
    "cover": "2. A ∨ H истинна при любом x, если везде, где H ложно, x ∈ A: "
             "A содержит множество, где H ложно.",
    "avoid": "2. ¬A ∨ H истинна при любом x, если везде, где H ложно, x ∉ A: "
             "A не пересекается с множеством, где H ложно.",
    "both": "2. Формула — конъюнкция двух условий, обе скобки должны быть истинны всегда. "
            "Из (¬A ∨ H1): там, где H1 ложно, x ∉ A. Из (A ∨ H2): там, где H2 ложно, x ∈ A.",
    "differ": "3. Выражения (A ∨ G) и H различны при каждом x. Где H истинно, A ∨ G должно быть ложным: "
              "x ∉ A и G ложно. Где H ложно, A ∨ G должно быть истинным: x ∈ A или G истинно. "
              "Отсюда: A не пересекается с множеством, где H истинно; A содержит множество "
              "«H ложно и G ложно»; G не пересекается с H.",
}


def line_task(kind, rnd, p, number):
    base = kind.partition("_")[0]
    want = "min" if kind in ("cover", "both_min", "differ_min") else "max"
    names = LINE_NAMES[:p.n_intervals]
    ivs = rand_intervals(rnd, names)
    ctx = Ctx(rnd, lambda: line_lit(rnd, names))
    A = ("in", "A")
    steps, sched = pick_schedule(rnd, p, kind)
    h = lambda: rand_h(ctx.lit, rnd, rnd.choice((1, 2)))
    parts = {}
    if base == "cover":
        parts["H"] = h()
        cores = [("or", A, parts["H"])]
    elif base == "avoid":
        parts["H"] = h()
        cores = [("or", ("not", A), parts["H"])]
    elif base == "both":
        parts["H1"], parts["H2"] = h(), h()
        cores = [("and", ("or", ("not", A), parts["H1"]), ("or", A, parts["H2"]))]
    else:                                                    # differ
        parts["G"] = ctx.lit() if rnd.random() < 0.6 else rand_h(ctx.lit, rnd, 1)
        parts["H"] = h()
        cores = [("or", A, parts["G"]), parts["H"]]
    if len(cores) == 1:
        chains = [sched]
    else:
        k1 = (len(sched) + 1) // 2
        chains = [sched[:k1], sched[k1:]]

    finals, hists = [], []
    for core, ch in zip(cores, chains):
        out, why = obfuscate(core, ch, ctx)
        if out is None:
            return None, why
        finals.append(out[0])
        hists.append(out[1])
    if ("in", "A") not in leaves(finals[0]):
        return None, "A выпало из формулы"
    core_vars = {n for c in cores for _, n in leaves(c) if n != "A"}
    shown = core_vars | {n for f in finals for _, n in leaves(f) if n != "A"}
    used = [n for n in names if n in shown]
    if len(used) < 2 or len(core_vars) < 2:
        return None, "в формуле меньше двух отрезков"
    L = Line({n: ivs[n] for n in used})

    def sets(Lx, log=None):
        if base == "cover":
            return evaluate(Lx, negate(parts["H"]), log), frozenset()
        if base == "avoid":
            return frozenset(), evaluate(Lx, negate(parts["H"]), log)
        if base == "both":
            O = evaluate(Lx, negate(parts["H1"]), log)
            I = evaluate(Lx, negate(parts["H2"]), log)
        else:
            SG = evaluate(Lx, parts["G"], log)
            SH = evaluate(Lx, parts["H"], log)
            if SG & SH:
                return None
            O, I = SH, Lx.all - SH - SG
        if not I or not O or I & O:
            return None
        return I, O

    def answer(Lx):
        s = sets(Lx)
        if s is None:
            return None
        r = solve(Lx, s[0], s[1], want)
        return r[0] if r else None

    log = []
    s = sets(L, log)
    if s is None:
        return None, "условия вырождены или противоречат друг другу"
    res = solve(L, s[0], s[1], want)
    if res is None:
        return None, "нет подходящего конечного A"
    ans, fin, lo, hi = res
    if base == "differ":
        cond = lambda env: ev(finals[0], env) != ev(finals[1], env)
    else:
        cond = lambda env: ev(finals[0], env)
    if not verify(L, cond, lo, hi):
        return None, "проверка ответа не прошла"
    if not all_matter(L, [n for n in used if n in core_vars], answer):
        return None, "какой-то отрезок не влияет на ответ"

    word = {2: "два отрезка", 3: "три отрезка", 4: "четыре отрезка"}[len(used)]
    qual = "наименьшую" if want == "min" else "наибольшую"
    intro = (f"На числовой прямой даны {word}: "
             + ", ".join(f"{n} = [{a}; {b}]" for n, (a, b) in L.ivs.items()) + ".")
    if base == "differ":
        text = (f"{intro} Определите {qual} возможную длину отрезка A, при выборе которого выражения\n"
                f"   {show(finals[0])}\nи\n   {show(finals[1])}\n"
                f"принимают различные значения при любых x.")
        lines = ["1. Упрощаем первое выражение:"] + chain_lines(finals[0], hists[0])
        lines.append(f"   Получили: {show(cores[0])}.")
        lines.append("2. Упрощаем второе выражение:" if hists[1] else "2. Второе выражение уже простое:")
        lines += chain_lines(finals[1], hists[1])
        lines.append(f"   Обозначим G = {show(parts['G'])}, H = {show(parts['H'])}.")
    else:
        text = (f"{intro} Укажите {qual} возможную длину такого отрезка A, что формула\n"
                f"   {show(finals[0])}\n"
                f"тождественно истинна, то есть принимает значение 1 при любом значении переменной x.")
        lines = ["1. Упрощаем формулу законами логики:"] + chain_lines(finals[0], hists[0])
        desc = ", ".join(f"{k} = {show(v)}" for k, v in parts.items())
        lines.append(f"   Получили: {show(cores[0])},  где {desc}.")
    lines.append(REASON[base])
    lines.append("Множества на прямой:" if base == "differ" else "3. Множества на прямой:")
    lines += [f"   {n} = {L.fmt(L.atom[n])}" for n in used]
    lines += [f"   {show(f)}:  {L.fmt(r)}   [{how}]" for f, r, how in log]
    if base != "cover" and base != "avoid":
        lines.append(f"   A обязан содержать {L.fmt(s[0])} и не пересекать {L.fmt(s[1])}.")
    lines.append("Выбираем A:")
    lines += ["   " + x for x in fin]
    skeleton = (kind,) + tuple(law for hh in hists for law, _, _ in hh)
    return Task(number, kind, text, ans, lines, steps, list(dict.fromkeys(sched)), skeleton), None


# ---------------------------------------------------------------- виды 4-6: битовые операции
def b5(v):
    return format(v, f"0{NB}b")


def bits_task(kind, rnd, p, number):
    ctx = Ctx(rnd, lambda: bit_lit(rnd), lambda: bit_leaf(rnd))
    x, A = ("var", "x"), ("var", "A")
    H = rand_h(ctx.lit, rnd, rnd.choice((1, 2)))
    test = ("nz", ("band", x, A))
    core = {"bitmin": ("imp", H, test),
            "bitmax": ("imp", test, H),
            "bitmax0": ("imp", H, ("not", test))}[kind]
    want_max = kind != "bitmin"
    steps, sched = pick_schedule(rnd, p, kind)
    out, why = obfuscate(core, sched, ctx)
    if out is None:
        return None, why
    final, hist = out
    if not {("var", "x"), ("var", "A")} <= leaves(final):
        return None, "x или A выпали из формулы"
    xs = range(MASK + 1)

    def good(f, a):
        return all(ev(f, {"x": v, "A": a}) for v in xs)
    valid = [a for a in range(1, MASK + 1) if good(final, a)]
    if not valid or len(valid) == MASK:
        return None, "ответ тривиален или не существует"
    if valid != [a for a in range(1, MASK + 1) if good(core, a)]:
        return None, "ядро и итоговая формула разошлись (ошибка в правиле?)"
    Hs = [v for v in xs if ev(H, {"x": v})]
    Hn = [v for v in xs if not ev(H, {"x": v})]
    if not Hs or not Hn:
        return None, "H постоянна и не влияет на ответ"
    ans = max(valid) if want_max else min(valid)

    def sset(S):
        sh = ", ".join(f"{v} ({b5(v)})" for v in S[:8])
        return "{" + sh + (", …" if len(S) > 8 else "") + f"}}  — всего {len(S)}"

    def union(S):
        o = 0
        for v in S:
            o |= v
        return o

    used = {n[0] for _, n in subterms(final)}
    opnames = {"band": "& — поразрядное И", "bor": "| — поразрядное ИЛИ",
               "bxor": "^ — поразрядное исключающее ИЛИ", "bnot": f"~ — поразрядное НЕ ({NB} бит)"}
    note = "; ".join(v for k, v in opnames.items() if k in used)
    qual = "наибольшее" if want_max else "наименьшее"
    text = (f"Найдите {qual} натуральное число A (A ≤ {MASK}), при котором формула\n"
            f"   {show(final)}\n"
            f"тождественно истинна (равна 1) при любом целом x от 0 до {MASK}. ({note}.)")
    lines = ["1. Упрощаем формулу законами логики и битовыми тождествами:"] + chain_lines(final, hist)
    lines.append(f"   Получили: {show(core)},  где H = {show(H)}.")
    if kind == "bitmin":
        lines += ["2. H → (x & A ≠ 0) истинно при любом x, если у каждого x, где H истинно, "
                  "есть общий бит с A.",
                  f"   H истинно при x ∈ {sset(Hs)}",
                  "   Подбираем наименьшее A, у которого есть общий бит с каждым из этих x."]
    elif kind == "bitmax":
        o = union(Hn)
        lines += ["2. (x & A ≠ 0) → H истинно при любом x, если у A нет общих битов "
                  "ни с одним x, где H ложно.",
                  f"   H ложно при x ∈ {sset(Hn)}",
                  f"   Объединение их битов: {b5(o)}; A может использовать только остальные биты: "
                  f"наибольшее A = {b5(MASK & ~o)} = {MASK & ~o}."]
    else:
        o = union(Hs)
        lines += ["2. H → (x & A = 0) истинно при любом x, если у A нет общих битов "
                  "ни с одним x, где H истинно.",
                  f"   H истинно при x ∈ {sset(Hs)}",
                  f"   Объединение их битов: {b5(o)}; наибольшее A = {b5(MASK & ~o)} = {MASK & ~o}."]
    lines.append(f"3. A = {ans} ({b5(ans)}) подходит: формула истинна при всех x от 0 до {MASK} (перебор).")
    a2 = ans + 1 if want_max else ans - 1
    if 1 <= a2 <= MASK:
        cx = next(v for v in xs if not ev(final, {"x": v, "A": a2}))
        lines.append(f"   A = {a2} ({b5(a2)}) не подходит: при x = {cx} ({b5(cx)}) формула ложна "
                     f"(H {'истинно' if ev(H, {'x': cx}) else 'ложно'}, "
                     f"x & A {'≠' if cx & a2 else '='} 0).")
    skeleton = (kind,) + tuple(law for law, _, _ in hist)
    return Task(number, kind, text, ans, lines, steps, list(dict.fromkeys(sched)), skeleton), None


KINDS = {       # вид -> функция (rnd, params, number) -> (Task | None, причина неудачи)
    "cover": partial(line_task, "cover"),            # прямая: A ∨ H, наименьшая длина
    "avoid": partial(line_task, "avoid"),            # прямая: ¬A ∨ H, наибольшая длина
    "both_min": partial(line_task, "both_min"),      # прямая: (¬A ∨ H1) ∧ (A ∨ H2), наименьшая
    "both_max": partial(line_task, "both_max"),      # то же, наибольшая
    "differ_min": partial(line_task, "differ_min"),  # прямая: «выражения различны при любом x»
    "differ_max": partial(line_task, "differ_max"),
    "bitmin": partial(bits_task, "bitmin"),          # биты: H → (x & A ≠ 0), наименьшее A
    "bitmax": partial(bits_task, "bitmax"),          # биты: (x & A ≠ 0) → H, наибольшее A
    "bitmax0": partial(bits_task, "bitmax0"),        # биты: H → (x & A = 0), наибольшее A
}


# ============================================================ генерация
def generate_tasks(n=5, seed=None, params=None, max_attempts=4000, verbose=True):
    p = params or TaskParams()
    bad = [t for t in (p.topics or ()) if t not in TOPICS]
    if bad:
        raise ValueError(f"неизвестные темы: {bad}; есть: {list(TOPICS)}")
    kinds = tuple(p.kinds or KINDS)
    badk = [k for k in kinds if k not in KINDS]
    if badk:
        raise ValueError(f"неизвестные виды: {badk}; есть: {list(KINDS)}")
    rnd = random.Random(seed)
    out, seen_text, seen_sk, fails = [], set(), set(), Counter()
    for _ in range(max_attempts):
        if len(out) >= n:
            break
        kind = rnd.choice(kinds)
        task, why = KINDS[kind](rnd, p, len(out) + 1)
        if task is None:
            fails[(kind, why)] += 1
        elif task.text in seen_text:
            fails[(kind, "повтор условия")] += 1
        elif p.unique_skeleton and task.skeleton in seen_sk:
            fails[(kind, "повтор скелета")] += 1
        else:
            seen_text.add(task.text)
            seen_sk.add(task.skeleton)
            out.append(task)
    if len(out) < n and verbose:
        print(f"Найдено {len(out)} из {n}. Причины неудач:")
        for (k, why), c in fails.most_common(8):
            print(f"  [{k}] {why}: {c} раз")
    return out


def print_tasks(tasks, solutions=True):
    for t in tasks:
        print(t.statement(), "\n")
    if solutions:
        print("=" * 20, "РЕШЕНИЯ", "=" * 20)
        for t in tasks:
            print(t.solution_text(), "\n")


if __name__ == "__main__":
    tasks = generate_tasks(4, seed=1, params=TaskParams(
        kinds=("cover", "avoid", "both_min", "both_max", "differ_min", "differ_max"),
        topics=("morgan", "implication", "constants"), steps=3))
    bits = generate_tasks(3, seed=2, params=TaskParams(
        kinds=("bitmin", "bitmax", "bitmax0"),
        topics=("const_split", "distributivity", "bit_test"), steps=3))
    tasks += bits
    for i, t in enumerate(tasks, 1):
        t.number = i
    print_tasks(tasks)
    rule_report()