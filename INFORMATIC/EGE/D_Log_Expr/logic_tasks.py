"""Задачи-генераторы: виды KINDS, сборка условия и решения, generate_tasks.

Перенесено из `tests/didactics.py` (строки 764-1098). Поведение сохранено, кроме
одной правки: all_matter вызывается на всех отрезках, напечатанных в условии
(used), а не только на отрезках ядра, -- иначе в условие мог попасть отрезок,
который на ответ не влияет.

Вход: TaskParams. Выход: Task (number, kind, text, answer, solution, steps,
topics, skeleton). Для API берётся Task.text -- без префикса «Задача N.».
"""
import random
from collections import Counter
from dataclasses import dataclass
from functools import partial

try:
    from .logic_core import (
        LINE_NAMES, MASK, NB, Line, all_matter, evaluate, ev, leaves, negate,
        show, show_tex, solve, subterms, verify,
    )
    from .logic_rules import (
        BIT_ONLY, TOPICS, Ctx, bit_leaf, bit_lit, line_lit, obfuscate, rand_h,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from logic_core import (
        LINE_NAMES, MASK, NB, Line, all_matter, evaluate, ev, leaves, negate,
        show, show_tex, solve, subterms, verify,
    )
    from logic_rules import (
        BIT_ONLY, TOPICS, Ctx, bit_leaf, bit_lit, line_lit, obfuscate, rand_h,
    )


# ============================================================ параметры и задачи
@dataclass
class TaskParams:
    kinds: tuple = None             # None = все виды из KINDS
    topics: tuple = None            # None = все подходящие теме задачи (см. default_topics)
    steps: object = (2, 4)          # число преобразований: int или (мин, макс)
    n_intervals: int = 3            # 2..4 отрезка для задач на прямой
    each_topic: bool = True         # каждая выбранная тема встретится хотя бы раз
    unique_skeleton: bool = True    # не повторять одинаковую последовательность законов
    tex: bool = False               # condition в LaTeX ($$...$$) вместо Unicode-символов
    exact_intervals: bool = False   # true: в условии ровно n_intervals отрезков
    no_repeat_operands: bool = False  # true: запретить бинарные узлы с равными операндами


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

#: Бинарные логические операции logic_core, для которых проверяется повтор операндов.
NO_REPEAT_BINARY = ("and", "or", "imp", "eqv")


def has_repeat_operands(f):
    """True, если в f есть бинарный узел с двумя структурно равными операндами."""
    for _, node in subterms(f):
        if node[0] in NO_REPEAT_BINARY and node[1] == node[2]:
            return True
    return False


def line_task(kind, rnd, p, number, tex=False):
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
    if p.exact_intervals and len(used) != p.n_intervals:
        return None, "число отрезков в условии не совпало с intervals"
    if p.no_repeat_operands and "idempotency" not in (p.topics or ()):
        if any(has_repeat_operands(f) for f in finals):
            return None, "повтор одинаковых операндов"
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
    if not all_matter(L, used, answer):
        return None, "какой-то отрезок не влияет на ответ"

    sep, pad = SEP[tex]
    word = {2: "два отрезка", 3: "три отрезка", 4: "четыре отрезка"}[len(used)]
    qual = "наименьшую" if want == "min" else "наибольшую"
    intro = (f"На числовой прямой даны {word}: "
             + ", ".join(f"{n} = [{a}; {b}]" for n, (a, b) in L.ivs.items()) + ".")
    if base == "differ":
        text = (f"{intro} Определите {qual} возможную длину отрезка A, при выборе которого выражения{sep}"
                f"{pad}{fmt_formula(finals[0], tex)}{sep}и{sep}{pad}{fmt_formula(finals[1], tex)}{sep}"
                f"принимают различные значения при любых x.")
        lines = ["1. Упрощаем первое выражение:"] + chain_lines(finals[0], hists[0])
        lines.append(f"   Получили: {show(cores[0])}.")
        lines.append("2. Упрощаем второе выражение:" if hists[1] else "2. Второе выражение уже простое:")
        lines += chain_lines(finals[1], hists[1])
        lines.append(f"   Обозначим G = {show(parts['G'])}, H = {show(parts['H'])}.")
    else:
        text = (f"{intro} Укажите {qual} возможную длину такого отрезка A, что формула{sep}"
                f"{pad}{fmt_formula(finals[0], tex)}{sep}"
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


def fmt_formula(f, tex=False):
    """Формула внутри условия: в tex-режиме -- $$...$$, иначе show() как раньше."""
    return ("$$ " + show_tex(f) + " $$") if tex else show(f)


#: Как вставить формулу в текст: tex -> одна строка, Unicode -> три строки с отступом.
SEP = {True: (" ", ""), False: ("\n", "   ")}


def bits_task(kind, rnd, p, number, tex=False):
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
    sep, pad = SEP[tex]
    lim = (r"$A \le " + str(MASK) + "$") if tex else f"A ≤ {MASK}"
    text = (f"Найдите {qual} натуральное число A ({lim}), при котором формула{sep}"
            f"{pad}{fmt_formula(final, tex)}{sep}"
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


KINDS = {       # вид -> функция (rnd, params, number, tex) -> (Task | None, причина неудачи)
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
        task, why = KINDS[kind](rnd, p, len(out) + 1, p.tex)
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
