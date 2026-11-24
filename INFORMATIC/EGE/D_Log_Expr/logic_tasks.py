"""Задачи-генераторы: виды KINDS, сборка условия и решения, generate_tasks.

Перенесено из `tests/didactics.py` (строки 764-1098). Поведение сохранено, кроме
одной правки: all_matter вызывается на всех отрезках, напечатанных в условии
(used), а не только на отрезках ядра, -- иначе в условие мог попасть отрезок,
который на ответ не влияет.

Вход: TaskParams. Выход: Task (number, kind, text, answer, solution, steps,
topics, skeleton). Для API берётся Task.text -- без префикса «Задача N.».
"""
import copy
import random
from collections import Counter
from dataclasses import dataclass
from functools import partial

try:
    from .logic_core import (
        LINE_NAMES, MASK, MAX_SIZE, NB, INF, Line, all_matter, evaluate, ev,
        leaves, negate, show, show_tex, size, solve, subterms, verify,
    )
    from .logic_rules import (
        BIT_ONLY, TOPICS, Ctx, bit_leaf, bit_lit, line_lit, obfuscate, rand_h,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from logic_core import (
        LINE_NAMES, MASK, MAX_SIZE, NB, INF, Line, all_matter, evaluate, ev,
        leaves, negate, show, show_tex, size, solve, subterms, verify,
    )
    from logic_rules import (
        BIT_ONLY, TOPICS, Ctx, bit_leaf, bit_lit, line_lit, obfuscate, rand_h,
    )

try:
    from task_errors import BudgetError
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "..")
    ))
    from task_errors import BudgetError


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


#: Темы, допустимые для задач на числовой прямой (без битовых тем).
LINE_TOPICS = tuple(t for t in TOPICS if t not in BIT_ONLY)


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


# ---------------------------------------------------------------- задачи из facts
#: Допустимые имена фактов: P..U -- только имена отрезков, без ролей границ A.
FACT_NAMES = ("P", "Q", "R", "S", "T", "U")

#: Ключи фактов-делителей ДЕЛ(x, m): D1..D6 -- те же модули, что a..f.
DIV_FACT_NAMES = ("D1", "D2", "D3", "D4", "D5", "D6", "a", "b", "c", "d", "e", "f")

#: Границы модуля в ДЕЛ(x, m): как MIN_MODULUS/MAX_MODULUS в logic_div.
MIN_FACT_MODULUS, MAX_FACT_MODULUS = 2, 999

#: Сколько делителей допускается в гибридных facts.
MAX_DIV_FACTS = 6

#: Преамбула условия, если в формуле появляется ДЕЛ(n, m).
DIV_PREAMBLE = ("Обозначим через ДЕЛ(n, m) утверждение «натуральное число n "
                "делится без остатка на натуральное число m». ")

#: Вопросы, которые можно задать уже построенному условию.
FACT_QUESTIONS = (
    ("min_length", "min"), ("max_length", "max"),
    ("min_value", "min"), ("max_value", "max"),
)

#: Сколько схем держать активными в раундах запутывания. При 1-2 фактах схем
#: не больше 14, поэтому потолок ни на что не влияет; при 3..6 фактах пул
#: содержит сотни схем, а для выбора по seed достаточно 20 активных.
MAX_ACTIVE_SPECS = 20


@dataclass
class FactsTask:
    """Условие, построенное по facts; вопросы применяются без пересборки.

    `inner` -- множество, которое A обязан содержать; `outer` -- множество,
    которого A не должен касаться. Конкретная пара inner/outer соответствует
    одному из внутренних правил (I ⊆ A ⊆ U или U ⊆ A), а `answers` считаются
    уже после принятия итоговой формулы.
    """
    intervals: dict
    inner: frozenset
    outer: frozenset
    final: tuple
    core: tuple
    hist: list
    steps: int
    topics: tuple
    schedule: list
    line: Line
    answers: dict
    available: tuple
    selected_question: str
    tex: bool = True
    scheme: str = ""
    divisors: dict = None

    def answer_for(self, question):
        """Ответ на вопрос по уже построенному условию."""
        if question not in self.answers:
            raise ValueError(
                "question=%s недоступен; доступны: %s"
                % (question, ", ".join(self.available))
            )
        return int(self.answers[question])

    def condition_for(self, question):
        """Текст условия с формулировкой выбранного вопроса."""
        if question not in self.answers:
            raise ValueError(
                "question=%s недоступен; доступны: %s"
                % (question, ", ".join(self.available))
            )
        qual = "наименьшую" if question == "min_length" else "наибольшую"
        word = {1: "один отрезок", 2: "два отрезка", 3: "три отрезка",
                4: "четыре отрезка", 5: "пять отрезков",
                6: "шесть отрезков"}.get(len(self.intervals),
                                         "%d отрезков" % len(self.intervals))
        intro = ("На числовой прямой дан %s: " % word
                 if len(self.intervals) == 1 else
                 "На числовой прямой даны %s: " % word)
        intro += (", ".join("%s = [%s; %s]" % (name, lo, hi)
                            for name, (lo, hi) in self.intervals.items())
                  + ".")
        if self.divisors:
            intro = DIV_PREAMBLE + intro
        sep, pad = SEP[self.tex]
        if question in ("min_value", "max_value"):
            qual = ("наибольшего" if question == "max_value"
                    else "наименьшего")
            return (f"{intro} Для какого {qual} натурального числа A формула"
                    f"{sep}{pad}{fmt_formula(self.final, self.tex)}{sep}"
                    "тождественно истинна, то есть принимает значение 1 при "
                    "любом натуральном значении переменной x.")
        what = "такого отрезка A"
        if question == "max_length" and self.divisors:
            what += " с целыми концами"
        tail = ("при любом натуральном значении переменной x." if self.divisors
                else "при любом значении переменной x.")
        return (f"{intro} Укажите {qual} возможную длину {what}, "
                f"что формула{sep}{pad}{fmt_formula(self.final, self.tex)}{sep}"
                f"тождественно истинна, то есть принимает значение 1 {tail}")

    @property
    def condition(self):
        return self.condition_for(self.selected_question)

    @property
    def answer(self):
        return self.answer_for(self.selected_question)


def _facts_formula(names, op):
    """Формула пересечения/объединения всех facts через литералы x ∈ имя."""
    nodes = [("in", name) for name in names]
    if not nodes:
        raise ValueError("facts: нужен хотя бы один отрезок")
    node = nodes[0]
    for other in nodes[1:]:
        node = (op, node, other)
    return node


# ---------------------------------------------------------------- реестр схем
#: Дескриптор множества на прямой: один объект даёт и формулу Φ, и множество
#: точек, поэтому отдельных лямбд «формула»/«множество» нет.
@dataclass(frozen=True)
class _SetExpr:
    """Множество из фактов: дерево inter/union/diff/symdiff/name.

    Элементы `args` -- либо имена фактов (str), либо вложенные `_SetExpr`
    (тогда формулы и множества считаются рекурсивно). Пустой `args` у
    inter/union означает «все факты в порядке order». Для плоских дескрипторов
    (только имена) формулы и множества совпадают с прежними побайтово.
    """

    kind: str                       # inter | union | diff | symdiff | name
    args: tuple = ()                # имена фактов и/или вложенные _SetExpr

    def _items(self, order):
        """Аргументы дескриптора: явные либо все факты в порядке order."""
        return self.args if self.args else tuple(order)

    def formula(self, order):
        """Φ_X: формула из литералов x ∈ имя; вложенные дескрипторы -- рекурсивно.

        inter/union/diff -- левая свёртка по аргументам, symdiff -- свёртка
        ¬(acc ≡ rhs). Исключение: симметрическая разность ровно двух имён
        остаётся прежней формулой (a ∧ ¬b) ∨ (¬a ∧ b), чтобы текст уже
        существующих схем `cover_symdiff` не менялся побайтово.
        """
        items = self._items(order)
        if self.kind == "name":
            return _child_formula(items[0], order)
        if self.kind == "inter":
            node = _child_formula(items[0], order)
            for item in items[1:]:
                node = ("and", node, _child_formula(item, order))
            return node
        if self.kind == "union":
            node = _child_formula(items[0], order)
            for item in items[1:]:
                node = ("or", node, _child_formula(item, order))
            return node
        if self.kind == "diff":
            node = _child_formula(items[0], order)
            for item in items[1:]:
                node = ("and", node, ("not", _child_formula(item, order)))
            return node
        if self.kind == "symdiff":
            if len(items) == 2 and all(isinstance(x, str) for x in items):
                a, b = items
                return ("or", ("and", ("in", a), ("not", ("in", b))),
                        ("and", ("not", ("in", a)), ("in", b)))
            node = _child_formula(items[0], order)
            for item in items[1:]:
                node = ("not", ("eqv", node, _child_formula(item, order)))
            return node
        raise ValueError("неизвестный дескриптор множества: %s" % self.kind)

    def evaluate(self, env, order, all_pts=None):
        """То же множество, но как frozenset элементов Line.

        `all_pts` (контрольные точки прямой) множеству не нужен: оно целиком
        берётся из env; параметр сохранён, чтобы вызовы `_child_eval` были
        однородными для имён и вложенных дескрипторов.
        """
        items = self._items(order)
        if self.kind == "name":
            return frozenset(_child_eval(items[0], env, order, all_pts))
        if self.kind == "inter":
            out = frozenset(_child_eval(items[0], env, order, all_pts))
            for item in items[1:]:
                out = out & _child_eval(item, env, order, all_pts)
            return out
        if self.kind == "union":
            out = frozenset(_child_eval(items[0], env, order, all_pts))
            for item in items[1:]:
                out = out | _child_eval(item, env, order, all_pts)
            return out
        if self.kind == "diff":
            out = frozenset(_child_eval(items[0], env, order, all_pts))
            for item in items[1:]:
                out = out - _child_eval(item, env, order, all_pts)
            return out
        if self.kind == "symdiff":
            out = frozenset(_child_eval(items[0], env, order, all_pts))
            for item in items[1:]:
                out = out ^ _child_eval(item, env, order, all_pts)
            return out
        raise ValueError("неизвестный дескриптор множества: %s" % self.kind)


def _child_formula(item, order):
    """Φ элемента дескриптора: рекурсия в `_SetExpr`, иначе литерал x ∈ имя."""
    if isinstance(item, _SetExpr):
        return item.formula(order)
    return ("in", item)


def _child_eval(item, env, order, all_pts=None):
    """Множество элемента дескриптора: рекурсия в `_SetExpr`, иначе env[имя]."""
    if isinstance(item, _SetExpr):
        return item.evaluate(env, order, all_pts)
    return frozenset(env[item])


@dataclass(frozen=True)
class _Scheme:
    """Схема вывода: форма, Φ_X, Φ_Y и вопросы с конечным ответом.

    form=cover    core=(Φ_X → A),           inner=X, outer=∅
    form=inside   core=(A → Φ_X),           inner=∅, outer=дополнение(X)
    form=between  core=(Φ_X → A)∧(A → Φ_Y), inner=X, outer=дополнение(Y)
    """

    name: str
    form: str                       # cover | inside | between
    x: _SetExpr
    questions: tuple
    y: _SetExpr = None
    legacy: bool = False

    def constraints(self, env, order, universe):
        """(inner, outer) или (None, None), если схема к фактам неприменима."""
        x = self.x.evaluate(env, order)
        if self.form == "inside":
            return frozenset(), frozenset(universe - x)
        if not x:
            return None, None
        if self.form == "cover":
            return x, frozenset()
        y = self.y.evaluate(env, order) if self.y else None
        if y is None or not x <= y:
            return None, None
        return x, frozenset(universe - y)

    def core(self, order):
        """Ядро до запутывания; A -- единственная роль отрезка A."""
        a = ("in", "A")
        phi_x = self.x.formula(order)
        if self.form == "cover":
            return ("imp", phi_x, a)
        if self.form == "inside":
            return ("imp", a, phi_x)
        return ("and", ("imp", phi_x, a), ("imp", a, self.y.formula(order)))


#: Дескрипторы, которые встречаются в нескольких схемах (одни и те же объекты).
_DIFF_PQ = _SetExpr("diff", ("P", "Q"))
_DIFF_QP = _SetExpr("diff", ("Q", "P"))

#: Реестр схем. Порядок фиксирован: первые две -- legacy, они же первые в
#: _facts_rule_specs, поэтому specs[0] остаётся побайтово прежним.
_SCHEMES = (
    _Scheme("i_subset_a_subset_u", "between", _SetExpr("inter"),
            ("min_length", "max_length"), _SetExpr("union"), legacy=True),
    _Scheme("u_subset_a", "cover", _SetExpr("union"), ("min_length",),
            legacy=True),
    _Scheme("cover_inter", "cover", _SetExpr("inter"), ("min_length",)),
    _Scheme("cover_diff_pq", "cover", _DIFF_PQ, ("min_length",)),
    _Scheme("cover_diff_qp", "cover", _DIFF_QP, ("min_length",)),
    _Scheme("cover_symdiff", "cover", _SetExpr("symdiff", ("P", "Q")),
            ("min_length",)),
    _Scheme("inside_union", "inside", _SetExpr("union"), ("max_length",)),
    _Scheme("inside_inter", "inside", _SetExpr("inter"), ("max_length",)),
    _Scheme("inside_diff_pq", "inside", _DIFF_PQ, ("max_length",)),
    _Scheme("inside_diff_qp", "inside", _DIFF_QP, ("max_length",)),
    _Scheme("between_diff_pq_p", "between", _DIFF_PQ,
            ("min_length", "max_length"), _SetExpr("name", ("P",))),
    _Scheme("between_diff_qp_q", "between", _DIFF_QP,
            ("min_length", "max_length"), _SetExpr("name", ("Q",))),
    _Scheme("between_inter_p", "between", _SetExpr("inter"),
            ("min_length", "max_length"), _SetExpr("name", ("P",))),
    _Scheme("between_inter_q", "between", _SetExpr("inter"),
            ("min_length", "max_length"), _SetExpr("name", ("Q",))),
)


#: Базовые n-арные схемы реестра: пустой args у _SetExpr означает «все факты»,
#: поэтому они работают при любом числе фактов и входят в пул для 3..6.
_MULTI_BASE_NAMES = ("i_subset_a_subset_u", "u_subset_a", "cover_inter",
                     "inside_union", "inside_inter")


def _pair_schemes(p, q):
    """Схемы на двух фактах p и q: параметризованный аналог `_SCHEMES`.

    Порядок схем и их имена повторяют реестр: для (p, q) == ("P", "Q") кортеж
    побайтово совпадает с `_SCHEMES` (это проверяет `logic_facts_selfcheck`),
    поэтому specs[0] и specs[1] остаются прежними и для остальных пар.
    """
    lp, lq = p.lower(), q.lower()
    diff_pq = _SetExpr("diff", (p, q))
    diff_qp = _SetExpr("diff", (q, p))
    return (
        _Scheme("i_subset_a_subset_u", "between", _SetExpr("inter"),
                ("min_length", "max_length"), _SetExpr("union"), legacy=True),
        _Scheme("u_subset_a", "cover", _SetExpr("union"), ("min_length",),
                legacy=True),
        _Scheme("cover_inter", "cover", _SetExpr("inter"), ("min_length",)),
        _Scheme("cover_diff_%s%s" % (lp, lq), "cover", diff_pq,
                ("min_length",)),
        _Scheme("cover_diff_%s%s" % (lq, lp), "cover", diff_qp,
                ("min_length",)),
        _Scheme("cover_symdiff", "cover", _SetExpr("symdiff", (p, q)),
                ("min_length",)),
        _Scheme("inside_union", "inside", _SetExpr("union"), ("max_length",)),
        _Scheme("inside_inter", "inside", _SetExpr("inter"), ("max_length",)),
        _Scheme("inside_diff_%s%s" % (lp, lq), "inside", diff_pq,
                ("max_length",)),
        _Scheme("inside_diff_%s%s" % (lq, lp), "inside", diff_qp,
                ("max_length",)),
        _Scheme("between_diff_%s%s_%s" % (lp, lq, lp), "between", diff_pq,
                ("min_length", "max_length"), _SetExpr("name", (p,))),
        _Scheme("between_diff_%s%s_%s" % (lq, lp, lq), "between", diff_qp,
                ("min_length", "max_length"), _SetExpr("name", (q,))),
        _Scheme("between_inter_%s" % lp, "between", _SetExpr("inter"),
                ("min_length", "max_length"), _SetExpr("name", (p,))),
        _Scheme("between_inter_%s" % lq, "between", _SetExpr("inter"),
                ("min_length", "max_length"), _SetExpr("name", (q,))),
    )


def _multi_orderings(order, intervals):
    """Уникальные упорядочения фактов: [(тег, seq)] в порядке появления.

    Теги: "" -- исходный порядок, "_pos" -- по возрастанию левого конца,
    "_len" -- по убыванию длины. Совпавшие кортежи отбрасываются, чтобы не
    дублировать выражения.
    """
    candidates = [
        ("", tuple(order)),
        ("_pos", tuple(sorted(order, key=lambda n: (intervals[n][0],
                                                     intervals[n][1], n)))),
        ("_len", tuple(sorted(order, key=lambda n: (intervals[n][0] - intervals[n][1],
                                                     -intervals[n][0], n)))),
    ]
    seen, uniq = set(), []
    for tag, seq in candidates:
        if seq in seen:
            continue
        seen.add(seq)
        uniq.append((tag, seq))
    return uniq


def _sub_variants(sub):
    """Варианты выражения подкортежа: [(тег, _SetExpr)]; все элементы входят.

    Для 2 фактов пять бинарных форм, для 3 -- шесть компактных форм; длиннее
    трёх не бывает (деление seq пополам при k <= 6).
    """
    sub = tuple(sub)
    if len(sub) == 1:
        return (("id", _SetExpr("name", sub)),)
    if len(sub) == 2:
        a, b = sub
        return (("union", _SetExpr("union", sub)),
                ("inter", _SetExpr("inter", sub)),
                ("diff", _SetExpr("diff", (a, b))),
                ("diff_rev", _SetExpr("diff", (b, a))),
                ("symdiff", _SetExpr("symdiff", (a, b))))
    a, b, c = sub[0], sub[1], sub[2]
    return (("union", _SetExpr("union", sub)),
            ("inter", _SetExpr("inter", sub)),
            ("symdiff", _SetExpr("symdiff", sub)),
            ("diff_ab_c", _SetExpr("diff", (_SetExpr("union", (a, b)), c))),
            ("diff_bc_a", _SetExpr("diff", (_SetExpr("union", (b, c)), a))),
            ("union_ab_bc", _SetExpr("union", (_SetExpr("inter", (a, b)),
                                               _SetExpr("inter", (b, c))))))


def _multi_exprs(seq):
    """Выражения одного порядка фактов: [(тег, expr, upper)].

    upper -- второе множество between-схемы (Φ_Y): обычно объединение всех
    фактов, для разностей чётных/нечётных -- сама часть, для head-выражений --
    первый факт. Все выражения содержат каждый факт seq хотя бы один раз.
    """
    seq = tuple(seq)
    k = len(seq)
    all_u = _SetExpr("union", seq)
    name_head = _SetExpr("name", (seq[0],))
    out = [("all_u", all_u, all_u)]

    chain = tuple(_SetExpr("inter", (seq[i], seq[i + 1]))
                  for i in range(k - 1))
    out.append(("chain_inter", _SetExpr("union", chain), all_u))

    pairs = [(seq[i], seq[i + 1]) for i in range(0, k - 1, 2)]
    if k % 2:
        pairs.append((seq[-2], seq[-1]))        # нечётный хвост -- ещё пара
    out.append(("pair_inter",
                _SetExpr("union", tuple(_SetExpr("inter", pr)
                                        for pr in pairs)), all_u))
    out.append(("pair_diff_lr",
                _SetExpr("union", tuple(_SetExpr("diff", pr)
                                        for pr in pairs)), all_u))
    out.append(("pair_diff_rl",
                _SetExpr("union", tuple(_SetExpr("diff", (pr[1], pr[0]))
                                        for pr in pairs)), all_u))
    out.append(("pair_symdiff",
                _SetExpr("union", tuple(_SetExpr("symdiff", pr)
                                        for pr in pairs)), all_u))

    evens = _SetExpr("union", seq[0::2])
    odds = _SetExpr("union", seq[1::2])
    out.append(("eo_inter", _SetExpr("inter", (evens, odds)), all_u))
    out.append(("eo_diff", _SetExpr("diff", (evens, odds)), evens))
    out.append(("oe_diff", _SetExpr("diff", (odds, evens)), odds))
    out.append(("eo_symdiff", _SetExpr("symdiff", (evens, odds)), all_u))
    out.append(("symdiff_all", _SetExpr("symdiff", seq), all_u))

    out.append(("head_diff_rest",
                _SetExpr("diff", (seq[0], _SetExpr("union", seq[1:]))),
                name_head))
    out.append(("rest_diff_head",
                _SetExpr("diff", (_SetExpr("union", seq[1:]), seq[0])), all_u))
    out.append(("head_inter_rest",
                _SetExpr("inter", (seq[0], _SetExpr("union", seq[1:]))),
                name_head))
    out.append(("init_diff_last",
                _SetExpr("diff", (_SetExpr("union", seq[:-1]), seq[-1])),
                all_u))

    m = k // 2
    left, right = seq[:m], seq[m:]
    for l_tag, l_expr in _sub_variants(left):
        for r_tag, r_expr in _sub_variants(right):
            for top in ("inter", "diff", "symdiff", "union"):
                out.append(("%s_%s_%s" % (l_tag, r_tag, top),
                            _SetExpr(top, (l_expr, r_expr)), all_u))
    return out


def _multi_fact_schemes(order, intervals):
    """Пул схем для 3..6 фактов: базовые n-арные плюс комбинаторные ядра.

    Каждая схема использует все факты order: базовые -- через пустой args
    (_SetExpr по всем фактам), остальные -- через выражения из `_multi_exprs`
    по каждому уникальному упорядочению. Дубликаты по (expr, upper) внутри
    пула отбрасываются; имена схем включают тег упорядочения и тег выражения.
    """
    order = tuple(order)
    if len(order) < 3:
        raise ValueError("_multi_fact_schemes: нужно не меньше трёх фактов")
    schemes = [scheme for scheme in _SCHEMES
               if scheme.name in _MULTI_BASE_NAMES]
    seen = set()
    for order_tag, seq in _multi_orderings(order, intervals):
        for tag, expr, upper in _multi_exprs(seq):
            key = (expr, upper)
            if key in seen:
                continue
            seen.add(key)
            schemes.append(_Scheme("cover%s_%s" % (order_tag, tag), "cover",
                                   expr, ("min_length",)))
            schemes.append(_Scheme("inside%s_%s" % (order_tag, tag), "inside",
                                   expr, ("max_length",)))
            schemes.append(_Scheme("between%s_%s" % (order_tag, tag),
                                   "between", expr,
                                   ("min_length", "max_length"), upper))
    return tuple(schemes)


def _scheme_candidates(order, intervals):
    """Схемы под число фактов: 1 -- только legacy, 2 -- пара p/q, 3+ -- пул."""
    if len(order) == 1:
        return tuple(scheme for scheme in _SCHEMES if scheme.legacy)
    if len(order) == 2:
        return _pair_schemes(order[0], order[1])
    return _multi_fact_schemes(order, intervals)


def _facts_env(intervals):
    """(Line, {имя: множество}, порядок фактов); проверки входа как раньше."""
    names = set(intervals)
    if not names:
        raise ValueError("facts: нужен хотя бы один отрезок")
    unknown = names - set(FACT_NAMES)
    if unknown:
        raise ValueError(
            "facts: допустимы %s, получены: %s"
            % (", ".join(FACT_NAMES), ", ".join(sorted(unknown)))
        )
    order = tuple(intervals)
    line = Line(dict(intervals))
    return line, {name: line.atom[name] for name in order}, order


def _span(S, line):
    """(lo, hi) -- границы выпуклой оболочки S; None для пустого множества."""
    if not S:
        return None
    return line.bounds(min(S))[0], line.bounds(max(S))[1]


def _positive(S, line):
    """True, если у S есть промежуток положительной длины (нужен min_length)."""
    span = _span(S, line)
    if span is None:
        return False
    lo, hi = span
    return lo != -INF and hi != INF and hi - lo > 0


def _positive_run(S, line):
    """True, если у S есть цельный кусок положительной длины (нужен max_length)."""
    return any(_positive(frozenset(run), line) for run in line.runs(S))


def _question_possible(inner, outer, question, line):
    """Может ли вопрос получить конечный ответ при данных inner/outer."""
    if question == "min_length":
        return _positive(inner, line)
    return _positive_run(line.all - outer, line)


def _questions_for(scheme, inner, outer, line):
    """Вопросы схемы, у которых есть конечный ответ (отсев по вопросу).

    Отсев идёт по вопросу, а не по схеме целиком, и по форме схемы:

    * cover: точечное или пустое X -> схемы нет вовсе. Для X из одной точки
      ответ min формально существовал бы (A=[min X; max X] имеет
      положительную длину), но задача вырождена, поэтому схема отбрасывается;
    * inside: если в X нет цельного промежутка положительной длины, схемы нет
      (A обязано лежать в X, а max длины нулевого промежутка не бывает);
    * between, включая legacy i_subset_a_subset_u: точечное X отбрасывает
      только min_length (A=[X; X] имеет нулевую длину), а max_length остаётся,
      если solve даёт конечный ответ.
    """
    keep = []
    for question in scheme.questions:
        if scheme.form == "cover":
            ok = _positive(inner, line)
        elif scheme.form == "inside":
            ok = _positive_run(line.all - outer, line)
        else:
            ok = _question_possible(inner, outer, question, line)
        if ok:
            keep.append(question)
    return tuple(keep)


@dataclass
class _Spec:
    """Применимая схема и её вопросы, у которых есть конечный ответ."""

    scheme: _Scheme
    core: tuple
    inner: frozenset
    outer: frozenset
    questions: tuple

    @property
    def name(self):
        return self.scheme.name

    def constraints(self, env, order, universe):
        return self.scheme.constraints(env, order, universe)


def _scheme_specs(intervals, question=None):
    """Применимые схемы: отсев по вопросу, вырожденности и дубликатам.

    Порядок отсева: (а) вопрос не входит в схему; (б) вырожденность, причём по
    вопросу и по форме (см. `_questions_for`): cover с точечным X и inside без
    промежутка положительной длины исчезают целиком, between с точечным X
    теряет только min_length; (в) дубликаты по (core, inner, outer). Набор
    схем зависит от числа фактов (см. `_scheme_candidates`): 1 -- только
    legacy, 2 -- параметризованная пара p/q (для P и Q это прежние 14 схем),
    3..6 -- пул комбинаторных ядер `_multi_fact_schemes`.
    """
    line, env, order = _facts_env(intervals)
    specs, seen = [], set()
    for scheme in _scheme_candidates(order, intervals):
        if question is not None and question not in scheme.questions:
            continue
        inner, outer = scheme.constraints(env, order, line.all)
        if inner is None:
            continue
        questions = _questions_for(scheme, inner, outer, line)
        if not questions:
            continue
        core = scheme.core(order)
        key = (core, inner, outer)
        if key in seen:
            continue
        seen.add(key)
        specs.append(_Spec(scheme, core, inner, outer, questions))
    return line, specs


def _facts_rule_specs(intervals):
    """Legacy-схемы как раньше: (Line, [(core, что A содержит, чего нельзя)]).

    Возвращаются только две прежние схемы и без отсева вырожденности:
    ровно [I ⊆ A ⊆ U, U ⊆ A] при непустом пересечении и [U ⊆ A] иначе.
    """
    line, env, order = _facts_env(intervals)
    specs = []
    for scheme in _SCHEMES:
        if not scheme.legacy:
            continue
        inner, outer = scheme.constraints(env, order, line.all)
        if inner is None:
            continue
        specs.append((scheme.core(order), inner, outer))
    return line, specs


def facts_constraints(intervals):
    """Совместимый доступ к первому правилу: (Line, что A содержит, чего нельзя)."""
    line, specs = _facts_rule_specs(intervals)
    _, inner, outer = specs[0]
    return line, inner, outer


def facts_core(intervals):
    """Совместимый доступ к ядру первого правила до преобразований."""
    _, specs = _facts_rule_specs(intervals)
    return specs[0][0]


def pick_facts_schedule(rnd, steps, topics):
    """Ровно steps тем, причём каждая заказанная тема встречается хотя бы раз."""
    topics = list(topics)
    if not topics:
        raise ValueError("topics: нужна хотя бы одна тема")
    if steps < len(topics):
        raise ValueError(
            "steps=%d меньше числа явно заданных тем (%d)"
            % (steps, len(topics))
        )
    sched = topics + [rnd.choice(topics) for _ in range(steps - len(topics))]
    rnd.shuffle(sched)
    return sched


def _matters(line, env, order, spec, question, answer):
    """Влияет ли каждый факт на ответ именно на этот вопрос.

    Семантика та же, что у all_matter: факт по очереди заменяется на ∅ и на
    всю прямую, inner/outer пересчитываются из дескриптора схемы (Line
    копируется, меняется только atom), ответ сравнивается с базовым; None
    считается изменением. Как и all_matter, это эвристика: «не влияет»
    доказывается, а «влияет» -- нет, потому что проверены только две крайние
    замены, а не все промежуточные множества.
    """
    want = dict(FACT_QUESTIONS)[question]
    for name in order:
        same = 0
        for repl in (frozenset(), line.all):
            line2 = copy.copy(line)
            line2.atom = dict(line.atom)
            line2.atom[name] = repl
            inner, outer = spec.constraints(line2.atom, order, line2.all)
            if inner is None:
                continue
            res = solve(line2, inner, outer, want)
            if (res[0] if res else None) == answer:
                same += 1
        if same == 2:
            return False
    return True


@dataclass
class _State:
    """Состояние одной живой схемы в раундах генерации."""

    spec: _Spec
    rnd: object
    ctx: object
    questions: tuple
    base: dict
    task: object = None
    why: str = ""
    tries: int = 0                  # безуспешных попыток запутывания


def _build_facts_candidate(spec, rnd, ctx, line, intervals, topics, steps,
                           questions, base, tex):
    """Одна попытка схемы: расписание, запутывание, проверка ответа."""
    names = tuple(intervals)
    sched = pick_facts_schedule(rnd, steps, topics)
    out, why = obfuscate(spec.core, sched, ctx)
    if out is None:
        return None, why
    final, hist = out
    if len(hist) != steps:
        return None, "получилось не ровно steps преобразований"
    used = leaves(final)
    if ("in", "A") not in used:
        return None, "A выпало из формулы"
    if any(("in", name) not in used for name in names):
        return None, "какой-то отрезок выпал из формулы"
    available, answers = [], {}
    for question, _ in FACT_QUESTIONS:
        if question not in questions:
            continue
        ans, _, lo, hi = base[question]
        if not verify(line, lambda env: ev(final, env), lo, hi):
            continue
        available.append(question)
        answers[question] = int(ans)
    if not available:
        return None, "у условия нет конечного вопроса"
    return FactsTask(
        intervals=dict(intervals), inner=spec.inner, outer=spec.outer,
        final=final, core=spec.core, hist=hist, steps=steps,
        topics=tuple(topics), schedule=sched, line=line, answers=answers,
        available=tuple(available), selected_question=available[0], tex=tex,
        scheme=spec.name,
    ), None


def _build_facts_candidates(intervals, topics, steps, seed, tex=True,
                            max_attempts=2000, question=None):
    """Раунды по живым схемам в порядке реестра при общем бюджете попыток.

    Одна попытка на схему за раунд; схема выбывает после первого успеха,
    неуспех одной схемы вызов не валит -- причина попадает в отчёт. Фильтр
    влияния факта на вопрос применяется здесь, на уровне кандидата и вопроса,
    и может только сократить список вопросов схемы. У каждой схемы свой
    random.Random(seed), созданный один раз на вызов.

    Активных схем не больше `MAX_ACTIVE_SPECS`: при 3..6 фактах реестр даёт
    сотни схем, и перебирать их все после первых двадцати прошедших solve и
    `_matters` незачем. Если хотя бы одна схема уже построила задачу, схема,
    сделавшая `fair_share` безуспешных попыток, выбывает -- иначе одна
    несовместимая с темой схема сожгла бы остаток бюджета. Пока ни одна задача
    не построена, бюджет расходуется как раньше, вплоть до max_attempts.
    """
    line, specs = _scheme_specs(intervals, question)
    topics = tuple(topics)
    order = tuple(intervals)
    env = {name: line.atom[name] for name in order}
    states, reasons = [], []
    for spec in specs:
        if len(states) >= MAX_ACTIVE_SPECS:
            break
        base, questions = {}, []
        for q, want in FACT_QUESTIONS:
            if q not in spec.questions:
                continue
            res = solve(line, spec.inner, spec.outer, want)
            if res is None:
                continue
            if not _matters(line, env, order, spec, q, res[0]):
                continue
            base[q] = res
            questions.append(q)
        if not questions:
            reasons.append("%s: факты не влияют на вопрос" % spec.name)
            continue
        rnd = random.Random(seed)
        ctx = Ctx(rnd, lambda rnd=rnd: line_lit(rnd, order))
        states.append(_State(spec, rnd, ctx, tuple(questions), base))

    attempts = 0
    total = len(states)
    fair_share = (max(10, (max_attempts + total - 1) // total)
                  if total else 0)
    while attempts < max_attempts:
        built = any(st.task is not None for st in states)
        alive = [st for st in states
                 if st.task is None and not (built and st.tries >= fair_share)]
        if not alive:
            break
        for st in alive:
            if attempts >= max_attempts:
                break
            attempts += 1
            st.tries += 1
            task, why = _build_facts_candidate(
                st.spec, st.rnd, st.ctx, line, intervals, topics, steps,
                st.questions, st.base, tex,
            )
            if task is None:
                st.why = why
            else:
                st.task = task
    candidates = [st.task for st in states if st.task is not None]
    reasons.extend("%s: %s" % (st.spec.name, st.why or "бюджет исчерпан")
                   for st in states if st.task is None)
    return candidates, reasons

# ---------------------------------------------------------------- гибриды: отрезки + ДЕЛ
#: Порог активных гибридных схем в раундах запутывания (как MAX_ACTIVE_SPECS).
MAX_ACTIVE_HYBRID_SPECS = 20


def _split_facts(facts):
    """facts -> (intervals, divisors): отрезки P..U и модули ДЕЛ(x, m).

    Делитель -- целое из MIN_FACT_MODULUS..MAX_FACT_MODULUS под ключом a..f или
    D1..D6. Делители допустимы только вместе хотя бы с одним отрезком, при их
    наличии границы отрезков натуральны, модули не повторяются.
    """
    intervals, divisors = {}, {}
    for name, value in facts.items():
        if name in FACT_NAMES:
            try:
                pair = tuple(value)
            except TypeError:
                pair = ()
            if len(pair) != 2 or any(isinstance(v, bool) or not isinstance(v, int)
                                     for v in pair):
                raise ValueError(
                    "facts.%s: ожидается [левая; правая], получено %r"
                    % (name, value)
                )
            lo, hi = pair
            if lo >= hi:
                raise ValueError(
                    "facts.%s: левая граница должна быть меньше правой" % name
                )
            intervals[name] = (lo, hi)
            continue
        if name in DIV_FACT_NAMES:
            modulus = value
            if isinstance(modulus, bool) or not isinstance(modulus, int):
                raise ValueError(
                    "facts.%s: ожидается целое число-делитель, получено %r"
                    % (name, value)
                )
            if not MIN_FACT_MODULUS <= modulus <= MAX_FACT_MODULUS:
                raise ValueError(
                    "facts.%s: делитель должен быть от %d до %d, получено %d"
                    % (name, MIN_FACT_MODULUS, MAX_FACT_MODULUS, modulus)
                )
            divisors[name] = modulus
            continue
        raise ValueError(
            "facts: допустимы %s и делители %s; неизвестны: %s"
            % (", ".join(FACT_NAMES), ", ".join(DIV_FACT_NAMES), name)
        )
    if divisors:
        if not intervals:
            raise ValueError("facts: нужен хотя бы один отрезок P..U")
        if len(divisors) > MAX_DIV_FACTS:
            raise ValueError(
                "facts: делителей не больше %d, получено %d"
                % (MAX_DIV_FACTS, len(divisors))
            )
        moduli = list(divisors.values())
        if len(set(moduli)) != len(moduli):
            raise ValueError(
                "facts: делители не должны повторяться, получено %s"
                % ", ".join(str(m) for m in moduli)
            )
        for name, (lo, _hi) in intervals.items():
            if lo < 1:
                raise ValueError(
                    "facts.%s: при наличии делителей левая граница должна "
                    "быть не меньше 1" % name
                )
    return intervals, divisors


@dataclass(frozen=True)
class _HybridScheme:
    """Схема гибридной задачи: Φ_iv по отрезкам, Φ_div по атомам ДЕЛ и вопрос.

    family=cover    core = (Φ_iv ∧ Φ_div) → (x ∈ A)       -- min_length
    family=avoid    core = (x ∈ A) → (Φ_iv ∧ ¬Φ_div)      -- max_length
    family=div_max  core = (Φ_iv ∧ Φ_div) → ДЕЛ(x, A)     -- max_value
    family=div_min  core = ДЕЛ(x, A) → (¬Φ_iv ∨ Φ_div)    -- min_value

    Атомы делимости до подстановки: ``("in", "D<модуль>")`` и ``("in", "DA")``.
    """

    name: str
    family: str
    x: object
    div: tuple
    question: str

    def core(self, order):
        """Ядро до запутывания; order -- порядок отрезков в facts."""
        phi = self.x.formula(order)
        if self.family == "cover":
            return ("imp", ("and", phi, self.div), ("in", "A"))
        if self.family == "avoid":
            return ("imp", ("in", "A"), ("and", phi, ("not", self.div)))
        if self.family == "div_max":
            return ("imp", ("and", phi, self.div), ("in", "DA"))
        return ("imp", ("in", "DA"), ("or", ("not", phi), self.div))


def _div_atom(modulus):
    """Атом делимости до подстановки: ДЕЛ(x, modulus)."""
    return ("in", "D%d" % modulus)

def _hybrid_iv_pool(order):
    """Пул выражений Φ_iv по отрезкам: (метка, _SetExpr)."""
    k = len(order)
    if k == 1:
        return [("name", _SetExpr("name", order))]
    if k == 2:
        first, second = order
        return [
            ("inter", _SetExpr("inter", order)),
            ("union", _SetExpr("union", order)),
            ("diff_12", _SetExpr("diff", (first, second))),
            ("diff_21", _SetExpr("diff", (second, first))),
            ("symdiff", _SetExpr("symdiff", (first, second))),
        ]
    seq = order
    chain = tuple(_SetExpr("inter", (seq[i], seq[i + 1]))
                  for i in range(k - 1))
    pairs = [(seq[i], seq[i + 1]) for i in range(0, k - 1, 2)]
    if k % 2:
        pairs.append((seq[-2], seq[-1]))
    evens = _SetExpr("union", seq[0::2])
    odds = _SetExpr("union", seq[1::2])
    return [
        ("union", _SetExpr("union", seq)),
        ("inter", _SetExpr("inter", seq)),
        ("chain_inter", _SetExpr("union", chain)),
        ("pair_inter", _SetExpr("union", tuple(
            _SetExpr("inter", pair) for pair in pairs))),
        ("pair_diff_lr", _SetExpr("union", tuple(
            _SetExpr("diff", pair) for pair in pairs))),
        ("eo_diff", _SetExpr("diff", (evens, odds))),
        ("head_diff_rest", _SetExpr("diff", (
            seq[0], _SetExpr("union", seq[1:])))),
    ]


def _hybrid_div_pool(moduli):
    """Пул выражений Φ_div по атомам ДЕЛ: (метка, формула)."""
    atoms = [_div_atom(modulus) for modulus in moduli]
    k = len(atoms)
    if k == 1:
        return [("div_m", atoms[0]), ("not_div_m", ("not", atoms[0]))]
    if k == 2:
        first, second = atoms
        return [
            ("lcm", ("and", first, second)),
            ("gcd_or", ("or", first, second)),
            ("diff_12", ("and", first, ("not", second))),
            ("diff_21", ("and", second, ("not", first))),
            ("xor_div", ("not", ("eqv", first, second))),
        ]
    chain_lcm = [("and", atoms[i], atoms[i + 1]) for i in range(k - 1)]
    chain_gcd = [("or", atoms[i], atoms[i + 1]) for i in range(k - 1)]
    pairs = [(atoms[i], atoms[i + 1]) for i in range(0, k - 1, 2)]
    if k % 2:
        pairs.append((atoms[-2], atoms[-1]))
    pool = [
        ("all_lcm", _fold("and", atoms)),
        ("all_gcd", _fold("or", atoms)),
        ("chain_lcm_gcd", _fold("or", chain_lcm)),
        ("chain_gcd_lcm", _fold("and", chain_gcd)),
        ("pair_lcm_gcd", _fold("or", [("and", a, b) for a, b in pairs])),
        ("isolate_lcm_gcd_0", ("or", _fold("and", atoms[1:]), atoms[0])),
        ("lcm_not_last", ("and", _fold("and", atoms[:-1]),
                          ("not", atoms[-1]))),
    ]
    seen, unique = set(), []
    for tag, node in pool:
        if node in seen:
            continue
        seen.add(node)
        unique.append((tag, node))
    return unique


#: Семейства гибридных схем: (family, вопрос, префикс имени).
HYBRID_FAMILIES = (
    ("cover", "min_length", "hyb_cover"),
    ("avoid", "max_length", "hyb_avoid"),
    ("div_max", "max_value", "hyb_div_max"),
    ("div_min", "min_value", "hyb_div_min"),
)


def _hybrid_schemes(intervals, divisors):
    """Все пары (Φ_iv, Φ_div) на три семейства: каждая пара даёт три схемы."""
    order = tuple(intervals)
    moduli = tuple(divisors.values())
    schemes, seen = [], set()
    for iv_tag, x in _hybrid_iv_pool(order):
        for div_tag, div in _hybrid_div_pool(moduli):
            for family, question, prefix in HYBRID_FAMILIES:
                key = (x, div, family)
                if key in seen:
                    continue
                seen.add(key)
                schemes.append(_HybridScheme(
                    "%s_%s_%s" % (prefix, iv_tag, div_tag),
                    family, x, div, question,
                ))
    return tuple(schemes)


def _gcd(a, b):
    """НОД двух натуральных чисел."""
    while b:
        a, b = b, a % b
    return a


def _longest_run(points):
    """Самый левый отрезок из подряд идущих чисел: (a, b) при b > a."""
    best, start, prev = None, None, None
    for x in sorted(points):
        if prev is None or x != prev + 1:
            if start is not None and prev > start:
                if best is None or prev - start > best[1] - best[0]:
                    best = (start, prev)
            start = x
        prev = x
    if start is not None and prev > start:
        if best is None or prev - start > best[1] - best[0]:
            best = (start, prev)
    return best


def _fold(op, items):
    """Левая свёртка списка узлов бинарной операцией op."""
    node = items[0]
    for item in items[1:]:
        node = (op, node, item)
    return node

def _iv_mask(expr, intervals, limit, over=None):
    """Точки 1..limit, где истинна Φ_iv; over заменяет литерал отрезка."""
    phi = expr.formula(tuple(intervals))
    over = over or {}
    points = set()
    for x in range(1, limit + 1):
        env = {name: lo <= x <= hi for name, (lo, hi) in intervals.items()}
        for name, value in over.items():
            env[name] = value
        if ev(phi, env):
            points.add(x)
    return frozenset(points)


def _div_mask(expr, moduli, limit, over=None):
    """Точки 1..limit, где истинна Φ_div; over заменяет атом "D<модуль>"."""
    over = over or {}
    points = set()
    for x in range(1, limit + 1):
        env = {"D%d" % m: x % m == 0 for m in moduli}
        for name, value in over.items():
            env[name] = value
        if ev(expr, env):
            points.add(x)
    return frozenset(points)


def _hyb_plan(scheme, intervals, moduli, limit, iv_over=None, div_over=None,
              div_fixed=None):
    """(ответ, отрезок A или None, множество S/W) при заданных заменах атомов."""
    iv = _iv_mask(scheme.x, intervals, limit, iv_over)
    if div_fixed is None:
        div = _div_mask(scheme.div, moduli, limit, div_over)
    else:
        div = frozenset(range(1, limit + 1)) if div_fixed else frozenset()
    if scheme.family == "avoid":
        active = iv - div
        run = _longest_run(active)
        if run is None:
            return None, None, active
        return run[1] - run[0], run, active
    active = iv & div
    if scheme.family == "cover":
        if len(active) < 2:
            return None, None, active
        lo, hi = min(active), max(active)
        return hi - lo, (lo, hi), active
    if scheme.family == "div_max":
        if not active:
            return None, None, active
        divisor = 0
        for x in active:
            divisor = _gcd(divisor, x)
        return ((divisor, None, active) if divisor >= 2
                else (None, None, active))
    for candidate in range(2, limit + 1):
        inside = [x for x in iv if x % candidate == 0]
        if inside and all(x in div for x in inside):
            return candidate, None, active
    return None, None, active


def _hybrid_matters(scheme, intervals, moduli, limit):
    """Влияют ли все отрезки и все делители; сдвигают ли делители ответ."""
    base, _place, focus = _hyb_plan(scheme, intervals, moduli, limit)
    if base is None:
        return False, "нет конечного ответа"
    for name in intervals:
        got = [
            _hyb_plan(scheme, intervals, moduli, limit, iv_over={name: value})
            for value in (False, True)
        ]
        answers = [ans for ans, _, _ in got]
        masks = [mask for _, _, mask in got]
        if not (any(ans != base for ans in answers)
                and any(mask != focus for mask in masks)):
            return False, "отрезок %s не влияет на ответ" % name
    for modulus in moduli:
        atom = "D%d" % modulus
        got = [
            _hyb_plan(scheme, intervals, moduli, limit,
                      div_over={atom: value})
            for value in (True, False)
        ]
        answers = [ans for ans, _, _ in got]
        masks = [mask for _, _, mask in got]
        if not (any(ans != base for ans in answers)
                and any(mask != focus for mask in masks)):
            return False, "делитель %d не влияет на ответ" % modulus
    if scheme.family == "cover":
        pure = _hyb_plan(scheme, intervals, moduli, limit, div_fixed=True)[0]
    elif scheme.family == "avoid":
        pure = _hyb_plan(scheme, intervals, moduli, limit, div_fixed=False)[0]
    else:
        pure = None
    if pure == base:
        return False, "делители не сдвигают ответ"
    return True, ""

def _hybrid_env(intervals, x, a):
    """Окружение для ev: литералы отрезков, x, A -- отрезок или число."""
    env = {name: lo <= x <= hi for name, (lo, hi) in intervals.items()}
    env["x"] = x
    env["A"] = (a[0] <= x <= a[1]) if isinstance(a, tuple) else a
    return env


def _verify_hybrid(final, intervals, question, answer, lo=None, hi=None):
    """Независимая проверка ответа перебором x = 1..X_max+2.

    Для min_length/max_length формула проверяется на A=[lo;hi]: минимальность
    -- через два максимальных собственных отрезка (монотонность по A), а
    максимальность -- через все отрезки длины answer+1 внутри 1..X_max+1.
    """
    limit = max(hi_point for _lo, hi_point in intervals.values())
    points = range(1, limit + 3)

    def works(a, xs=None):
        return all(ev(final, _hybrid_env(intervals, x, a))
                   for x in (points if xs is None else xs))

    if question == "min_length":
        return (works((lo, hi))
                and not works((lo + 1, hi))
                and not works((lo, hi - 1)))
    if question == "max_length":
        if not works((lo, hi)):
            return False
        for a in range(1, limit + 2):
            if works((a, a + answer + 1)):
                return False
        return True
    if question == "max_value":
        if not works(answer):
            return False
        for a in range(answer + 1, limit + 1):
            if works(a, range(1, limit + 1)):
                return False
        return True
    if not works(answer):
        return False
    for a in range(2, answer):
        if works(a, range(1, limit + 1)):
            return False
    return True


def _hybrid_substitute(final, moduli):
    """Подстановка атомов ДЕЛ: ("in","D<m>") -> ДЕЛ(x, m), ("in","DA") -> ДЕЛ(x, A)."""
    kind = final[0]
    if kind == "in":
        name = final[1]
        if name == "DA":
            return ("div", ("var", "x"), ("var", "A"))
        if name.startswith("D") and name[1:].isdigit():
            modulus = int(name[1:])
            if modulus in moduli:
                return ("div", ("var", "x"), ("c", modulus))
        return final
    if kind in ("var", "c", "tf"):
        return final
    return (kind,) + tuple(_hybrid_substitute(child, moduli)
                           for child in final[1:])


@dataclass
class _HybridSpec:
    """Применимая гибридная схема с готовым ответом."""

    scheme: _HybridScheme
    core: tuple
    answer: int
    place: tuple = None

    @property
    def name(self):
        return self.scheme.name

    @property
    def question(self):
        return self.scheme.question


def _hybrid_specs(intervals, divisors, question=None):
    """Применимые гибридные схемы: есть ответ, все отрезки и делители значимы."""
    moduli = tuple(divisors.values())
    order = tuple(intervals)
    limit = max(hi for _lo, hi in intervals.values())
    specs, reasons = [], []
    for scheme in _hybrid_schemes(intervals, divisors):
        if question is not None and scheme.question != question:
            continue
        core = scheme.core(order)
        if size(core) > MAX_SIZE:
            reasons.append("%s: ядро длиннее %d узлов"
                           % (scheme.name, MAX_SIZE))
            continue
        answer, place, focus = _hyb_plan(scheme, intervals, moduli, limit)
        if answer is None:
            reasons.append("%s: нет конечного ответа" % scheme.name)
            continue
        if (scheme.family == "avoid"
                and focus == _iv_mask(scheme.x, intervals, limit)):
            reasons.append("%s: делители ничего не вырезают" % scheme.name)
            continue
        ok, why = _hybrid_matters(scheme, intervals, moduli, limit)
        if not ok:
            reasons.append("%s: %s" % (scheme.name, why))
            continue
        specs.append(_HybridSpec(scheme, core, answer, place))
    return specs, reasons


@dataclass
class _HybridState:
    """Состояние одной активной гибридной схемы в раундах запутывания."""

    spec: _HybridSpec
    rnd: object
    ctx: object
    task: object = None
    why: str = ""
    tries: int = 0


def _build_hybrid_candidate(spec, rnd, ctx, intervals, divisors, topics, steps,
                            tex):
    """Одна попытка: запутать ядро и проверить итоговую формулу и ответ."""
    order = tuple(intervals)
    moduli = tuple(divisors.values())
    schedule = pick_facts_schedule(rnd, steps, topics)
    out, why = obfuscate(spec.core, schedule, ctx)
    if out is None:
        return None, why
    final, hist = out
    if len(hist) != steps:
        return None, "получилось не ровно steps преобразований"
    used = leaves(final)
    lost = [name for name in order if ("in", name) not in used]
    if lost:
        return None, "из формулы выпал отрезок %s" % ", ".join(lost)
    lost = [m for m in moduli if ("in", "D%d" % m) not in used]
    if lost:
        return None, ("из формулы выпал делитель %s"
                      % ", ".join(str(m) for m in lost))
    target = "A" if spec.scheme.family in ("cover", "avoid") else "DA"
    if ("in", target) not in used:
        return None, "из формулы выпало A"
    ast = _hybrid_substitute(final, moduli)
    if not _verify_hybrid(ast, intervals, spec.question, spec.answer,
                          *(spec.place or (None, None))):
        return None, "итоговая формула не подтвердила ответ %d" % spec.answer
    answers = {spec.question: spec.answer}
    return FactsTask(
        intervals=dict(intervals), inner=frozenset(), outer=frozenset(),
        final=ast, core=spec.core, hist=list(hist), steps=steps,
        topics=tuple(topics), schedule=schedule, line=None, answers=answers,
        available=(spec.question,), selected_question=spec.question, tex=tex,
        scheme=spec.name, divisors=dict(divisors),
    ), None


def _build_hybrid_candidates(intervals, divisors, topics, steps, seed,
                             tex=True, max_attempts=2000, question=None):
    """Раунды по живым гибридным схемам при общем бюджете попыток."""
    specs, reasons = _hybrid_specs(intervals, divisors, question)
    topics = tuple(topics)
    moduli = tuple(divisors.values())
    states = []
    for spec in specs:
        if len(states) >= MAX_ACTIVE_HYBRID_SPECS:
            break
        rnd = random.Random(seed)
        atoms = tuple(intervals) + tuple("D%d" % m for m in moduli)
        ctx = Ctx(rnd, lambda rnd=rnd, atoms=atoms: line_lit(rnd, atoms))
        states.append(_HybridState(spec, rnd, ctx))
    attempts, total = 0, len(states)
    fair_share = (max(10, (max_attempts + total - 1) // total)
                  if total else 0)
    while attempts < max_attempts:
        built = any(st.task is not None for st in states)
        alive = [st for st in states
                 if st.task is None and not (built and st.tries >= fair_share)]
        if not alive:
            break
        for st in alive:
            if attempts >= max_attempts:
                break
            attempts += 1
            st.tries += 1
            task, why = _build_hybrid_candidate(
                st.spec, st.rnd, st.ctx, intervals, divisors, topics, steps,
                tex,
            )
            if task is None:
                st.why = why
            else:
                st.task = task
    candidates = [st.task for st in states if st.task is not None]
    reasons.extend("%s: %s" % (st.spec.name, st.why or "бюджет исчерпан")
                   for st in states if st.task is None)
    return candidates, reasons


def _build_hybrid_facts_task(intervals, divisors, topics, steps, seed,
                             question=None, tex=True, max_attempts=2000):
    """Выбор подходящего гибридного кандидата по question и seed."""
    candidates, reasons = _build_hybrid_candidates(
        intervals, divisors, topics, steps, seed, tex=tex,
        max_attempts=max_attempts, question=question,
    )
    if not candidates:
        raise BudgetError(
            "не удалось построить гибридное условие за %d попыток: "
            "facts=%s, topics=%s, steps=%s, seed=%r; причины по схемам: %s"
            % (max_attempts, dict(intervals, **divisors), tuple(topics), steps,
               seed, "; ".join(reasons) if reasons else "нет применимых схем")
        )
    if question is not None:
        suitable = [task for task in candidates if question in task.answers]
        if not suitable:
            available = []
            for task in candidates:
                for q in task.available:
                    if q not in available:
                        available.append(q)
            raise ValueError(
                "question=%s недоступен; доступны: %s"
                % (question, ", ".join(available))
            )
        chosen = random.Random(seed).choice(suitable)
        chosen.selected_question = question
        return chosen
    choices = [(task, q) for task in candidates for q in task.available]
    chosen, selected = random.Random(seed).choice(choices)
    chosen.selected_question = selected
    return chosen




def build_facts_task(facts, topics, steps, seed, question=None, tex=True,
                     max_attempts=2000):
    """Построить варианты из facts и выбрать подходящий под question.

    Сначала по реестру строятся все применимые схемы: для двух фактов --
    прежние cover/inside/between на пересечении, объединении, разностях и
    симметрической разности, для 3..6 фактов -- комбинаторные ядерные
    выражения по всем фактам (`_multi_fact_schemes`). Затем question фильтрует
    уже полученные варианты: если у одной схемы нет максимума, запрос
    max_length может выбрать другую. Среди всех подходящих вариантов выбор
    детерминированно распределяется по seed, без предпочтения первого. Без
    question вариант и вопрос выбираются так же детерминированно по seed. При
    исчерпании бюджета -- BudgetError.

    Если в facts есть делители (a..f или D1..D6) вместе с отрезками, строится
    гибридное условие: Φ_iv по отрезкам и Φ_div по ДЕЛ(x, m), а вопрос может
    быть любым из min_length/max_length/min_value/max_value.
    """
    intervals, divisors = _split_facts(facts)
    if divisors:
        return _build_hybrid_facts_task(
            intervals, divisors, topics, steps, seed, question=question,
            tex=tex, max_attempts=max_attempts,
        )
    candidates, reasons = _build_facts_candidates(
        intervals, topics, steps, seed, tex=tex, max_attempts=max_attempts,
        question=question,
    )
    if not candidates:
        raise BudgetError(
            "не удалось построить условие по facts за %d попыток: facts=%s, "
            "topics=%s, steps=%s, seed=%r; причины по схемам: %s"
            % (max_attempts, dict(intervals), tuple(topics), steps, seed,
               "; ".join(reasons) if reasons else "нет применимых схем")
        )

    if question is not None:
        suitable = [task for task in candidates if question in task.answers]
        if not suitable:
            available = []
            for task in candidates:
                for q in task.available:
                    if q not in available:
                        available.append(q)
            raise ValueError(
                "question=%s недоступен; доступны: %s"
                % (question, ", ".join(available))
            )
        chosen = random.Random(seed).choice(suitable)
        chosen.selected_question = question
        return chosen

    choices = [(task, q) for task in candidates for q in task.available]
    chosen, selected = random.Random(seed).choice(choices)
    chosen.selected_question = selected
    return chosen


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
