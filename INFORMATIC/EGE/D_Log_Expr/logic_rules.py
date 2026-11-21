"""Реестр правил-теорем и цепочки проверенных преобразований.

Перенесено из `tests/didactics.py` (строки 182-627). Поведение сохранено, кроме
осознанных правок:
  * у четырёх ветвей r_imp_distr разные подписи (две помечены как обратные);
  * r_excluded_middle срабатывает и при обратном порядке операндов (симметрия);
  * probe_rule возвращает счётчики -- они нужны самопроверке.

Правило регистрируется декоратором @rule(topic) и имеет вид
(node, ctx) -> (новый_узел, "название закона") | None; кандидат принимается
только если тождественно равен текущей формуле (equiv).
"""
import os
import random
import sys
from collections import defaultdict

try:
    from .logic_core import (
        ASSOC, COMM, F, MASK, MAX_NOT_RUN, MAX_SIZE, NB, T, counterexample,
        equiv, is_bool, negate, not_run, replace, show, size, subterms,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from logic_core import (
        ASSOC, COMM, F, MASK, MAX_NOT_RUN, MAX_SIZE, NB, T, counterexample,
        equiv, is_bool, negate, not_run, replace, show, size, subterms,
    )


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
            "дистрибутивность → по конъюнкции в заключении: a → (b ∧ c) ≡ (a → b) ∧ (a → c)"
    if f[0] == "imp" and f[1][0] == "or":
        return ("and", ("imp", f[1][1], f[2]), ("imp", f[1][2], f[2])), \
            "дистрибутивность → по дизъюнкции в посылке: (a ∨ b) → c ≡ (a → c) ∧ (b → c)"
    if f[0] == "and" and f[1][0] == "imp" and f[2][0] == "imp":
        (a, b), (c, d) = f[1][1:], f[2][1:]
        if a == c:
            return ("imp", a, ("and", b, d)), \
                "обратная дистрибутивность, общий аргумент слева: (a → b) ∧ (a → d) ≡ a → (b ∧ d)"
        if b == d:
            return ("imp", ("or", a, c), b), \
                "обратная дистрибутивность, общий аргумент справа: (a → b) ∧ (c → b) ≡ (a ∨ c) → b"


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
    if f[0] == "or" and (f[2] == negate(f[1]) or f[1] == negate(f[2])):
        return T, "закон исключённого третьего: a ∨ ¬a ≡ 1"
    if f[0] == "and" and (f[2] == negate(f[1]) or f[1] == negate(f[2])):
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
    """Проверка гипотезы: как часто правило применимо и верно ли оно.

    Возвращает счётчики (применимо, верно, НЕВЕРНО, ошибок) -- их использует
    самопроверка, чтобы отличить «правило не нашло, где сработать» от
    «правило дало контрпример» и от исключения внутри правила.
    """
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
    return tried, ok, bad, err
