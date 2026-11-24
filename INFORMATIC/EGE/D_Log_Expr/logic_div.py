"""Задачи на делимость для ЕГЭ №15: факт ДЕЛ(x, m) как узел формулы.

Делимость -- это узел ``("div", ("var","x"), ("c",m))``, а не лист: в
``logic_core.py`` зарегистрированы ``OPS["div"]`` и ``TYPE["div"] = "bool"``, а
``show``/``show_tex`` печатают ``ДЕЛ(x, m)``. Поэтому ``ev``, ``size``,
``subterms``, ``replace``, ``negate``, ``leaves``, ``envs``, ``counterexample``
работают без правок.

Схемы (``a`` обязателен, ``b`` -- только у двухфактных D1/D2/D5)::

    D1  ДЕЛ(x,a) ∧ ДЕЛ(x,b) → ДЕЛ(x,A)   max_value, ответ НОК(a, b)
    D2  ДЕЛ(x,A) → ДЕЛ(x,a) ∧ ДЕЛ(x,b)   min_value, ответ НОК(a, b)
    D3  ДЕЛ(x,a) → ДЕЛ(x,A)              max_value, ответ a
    D4  ДЕЛ(x,A) → ДЕЛ(x,a)              min_value, ответ a
    D5  ДЕЛ(x,a) ∨ ДЕЛ(x,b) → ДЕЛ(x,A)   max_value, ответ НОД(a, b)

Запутывание идёт только по атомам: ДЕЛ-узлы заменяются на ``("in","D<модуль>")``
и ``("in","DA")``, законы логики применяются к атомному ядру, затем атомы
возвращаются в ДЕЛ-узлы. Законы -- схемы тавтологий, поэтому они верны при
любой интерпретации атомов; числовая эквивалентность при атомном запутывании
не считается, а проверяется отдельным оракулом в ``logic_div_selfcheck.py``.

Модули 2..999, НОК(a, b) <= 2520; в двухфактных схемах ни один модуль не делит
другой, у D5 дополнительно НОД > 1. Ответ проверяется по определению: период =
НОК(всех числовых модулей ядра, A), формула истинна при всех x из 1..период.

Для 3..6 модулей (DIV-UNLIM) реестр D1..D5 не подходит: ядро строится деревом
делимости ``_DivExpr`` из листьев ДЕЛ(x, m) и двух операций -- "and" (в решётке
делимости это НОК модулей) и "or" (НОД). Схемы перебираются по структурным
деревьям (сквозные НОК/НОД, цепочки, пары, чётные/нечётные, выделение одного
модуля, разбиение на половины), для каждого дерева берутся оба вопроса. Схема
попадает в пул, только если её ответ совпал с универсальным оракулом на периоде
НОК(moduli) и каждый модуль значим (_div_matters: неизбыточность на периоде и
чувствительность ответа). Период для k >= 3 -- до MAX_MULTI_PERIOD, ответ --
не меньше MIN_MULTI_ANSWER.

Публичные имена: DIV_TOPICS, DEFAULT_TOPICS, QUESTIONS, SCHEME_NAMES, DivTask,
build_div_task, check_moduli, check_topics, applicable_schemes, scheme_core,
scheme_answer, div_fact, div_fact_a, atom_map, to_atoms, from_atoms, gcd, lcm,
divisors, period, holds, max_size, MAX_MODULI, MAX_MULTI_PERIOD,
MAX_ACTIVE_DIV_SPECS, MIN_MULTI_ANSWER.

Только stdlib; от ``tests/``, ``task_api.py`` и ``logic_tasks.py`` (кроме
переиспользуемых помощников) не зависит.
"""
import random
from dataclasses import dataclass
from functools import lru_cache

try:
    from .logic_core import MAX_SIZE, ev, leaves, show, size
    from .logic_rules import BIT_ONLY, TOPICS, Ctx, obfuscate
    from .logic_tasks import (
        SEP, chain_lines, fmt_formula, has_repeat_operands, pick_facts_schedule,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from logic_core import MAX_SIZE, ev, leaves, show, size
    from logic_rules import BIT_ONLY, TOPICS, Ctx, obfuscate
    from logic_tasks import (
        SEP, chain_lines, fmt_formula, has_repeat_operands, pick_facts_schedule,
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


# ============================================================ параметры
MIN_MODULUS, MAX_MODULUS = 2, 999       # модули в ДЕЛ(x, m)
MAX_LCM = 2520                          # потолок НОК(a, b)
MAX_PERIOD = 2520                       # потолок периода для k <= 2 (== MAX_LCM)
MAX_MODULI = 6                          # допускается 1 <= len(moduli) <= 6, ключи a..f
MAX_MULTI_PERIOD = 10080                # потолок периода НОК(moduli) для k >= 3
MAX_ACTIVE_DIV_SPECS = 20               # сколько многофактных схем держим живыми
MIN_STEPS, MAX_STEPS = 1, 8             # число преобразований
MIN_ANSWER = 1                          # A -- натуральное число
MIN_MULTI_ANSWER = 2                    # при A = 1 ответ вырожден: ДЕЛ(x, 1) всегда 1

#: Вопросы задачи: наибольшее и наименьшее натуральное A.
QUESTIONS = ("max_value", "min_value")
QUESTION_WORD = {"max_value": "наибольшего", "min_value": "наименьшего"}

#: Темы логики без битовых: у ДЕЛ нет ни битовых листьев, ни чисел-констант.
DIV_TOPICS = tuple(t for t in TOPICS if t not in BIT_ONLY)

#: Темы по умолчанию, когда topics не заданы.
DEFAULT_TOPICS = ("implication", "morgan", "exportation", "impl_distr",
                  "distributivity", "absorption")

#: Имя атома для ДЕЛ(x, A); модули получают имена D<модуль>.
ATOM_A = "DA"


# ============================================================ арифметика
def gcd(a, b):
    """НОД по Евклиду (без math, чтобы не зависеть от версии stdlib)."""
    while b:
        a, b = b, a % b
    return a


def lcm(a, b):
    """НОК через НОД; для a, b >= 1."""
    return a // gcd(a, b) * b


def divisors(n):
    """Все натуральные делители n по возрастанию."""
    return [d for d in range(1, n + 1) if n % d == 0]


# ============================================================ факты и схемы
def div_fact(m):
    """Факт ДЕЛ(x, m) для числового модуля m."""
    return ("div", ("var", "x"), ("c", m))


def div_fact_a():
    """Факт ДЕЛ(x, A); A -- переменная, а не константа."""
    return ("div", ("var", "x"), ("var", "A"))


@dataclass(frozen=True)
class _Scheme:
    """Дескриптор схемы: имя, вопрос и нужен ли второй модуль b."""

    name: str
    question: str
    two: bool                       # True -- нужны a и b, False -- только a


#: Реестр схем в порядке выбора; ключ -- имя из условия.
_SCHEMES = {
    "D1": _Scheme("D1", "max_value", True),
    "D2": _Scheme("D2", "min_value", True),
    "D3": _Scheme("D3", "max_value", False),
    "D4": _Scheme("D4", "min_value", False),
    "D5": _Scheme("D5", "max_value", True),
}
SCHEME_NAMES = tuple(_SCHEMES)


def scheme_core(name, moduli):
    """Ядро схемы до запутывания; moduli -- (a,) или (a, b)."""
    a = moduli[0]
    if name == "D1":
        return ("imp", ("and", div_fact(a), div_fact(moduli[1])), div_fact_a())
    if name == "D2":
        return ("imp", div_fact_a(), ("and", div_fact(a), div_fact(moduli[1])))
    if name == "D3":
        return ("imp", div_fact(a), div_fact_a())
    if name == "D4":
        return ("imp", div_fact_a(), div_fact(a))
    if name == "D5":
        return ("imp", ("or", div_fact(a), div_fact(moduli[1])), div_fact_a())
    raise ValueError("неизвестная схема: %r; допустимы: %s"
                     % (name, ", ".join(SCHEME_NAMES)))


def scheme_answer(name, moduli):
    """Аналитический ответ схемы: НОК, НОД или сам модуль a."""
    a = moduli[0]
    if name in ("D1", "D2"):
        return lcm(a, moduli[1])
    if name == "D5":
        return gcd(a, moduli[1])
    if name in ("D3", "D4"):
        return a
    raise ValueError("неизвестная схема: %r; допустимы: %s"
                     % (name, ", ".join(SCHEME_NAMES)))


# ============================================================ дерево делимости
@dataclass(frozen=True)
class _DivExpr:
    """Дерево делимости: листья-модули и узлы «и» (НОК) и «или» (НОД).

    ``kind`` и ``items``:

    * ``"mod"`` -- ``items = (m,)``, лист ДЕЛ(x, m);
    * ``"and"`` -- ``items = (child_1, ...)``, левая свёртка ``∧``: в решётке
      делимости отвечает за НОК модулей (x кратно каждому из детей);
    * ``"or"`` -- ``items = (child_1, ...)``, левая свёртка ``∨``: НОД модулей
      (x кратно хотя бы одному ребёнку).

    Дети одного вида склеиваются (``and`` внутри ``and`` -- это снова ``and``),
    поэтому дерево всегда «переменное»: у ``and`` нет детей-``and``.
    Одноэлементные узлы схлопываются в ребёнка ещё в конструкторах ``_and``/
    ``_or``, так что у ``and``/``or`` всегда не меньше двух детей.
    """

    kind: str
    items: tuple

    def __post_init__(self):
        if self.kind == "mod":
            if (len(self.items) != 1 or isinstance(self.items[0], bool)
                    or not isinstance(self.items[0], int)):
                raise ValueError("_DivExpr: лист -- ровно один целый модуль, "
                                 "получено %r" % (self.items,))
            return
        if self.kind not in ("and", "or"):
            raise ValueError("_DivExpr: допустимы mod, and, or, получено %r"
                             % (self.kind,))
        if len(self.items) < 2:
            raise ValueError("_DivExpr: у %r должно быть не меньше двух детей"
                             % (self.kind,))
        for child in self.items:
            if not isinstance(child, _DivExpr):
                raise ValueError("_DivExpr: ребёнок должен быть _DivExpr, "
                                 "получено %r" % (child,))

    # ------------------------------------------------------------ построение
    def formula(self):
        """AST-узел формулы от x: листья -- ДЕЛ(x, m), узлы -- ∧ и ∨."""
        if self.kind == "mod":
            return div_fact(self.items[0])
        out = self.items[0].formula()
        for child in self.items[1:]:
            out = (self.kind, out, child.formula())
        return out

    def moduli(self):
        """Все листья-модули в порядке обхода дерева."""
        if self.kind == "mod":
            return (self.items[0],)
        out = ()
        for child in self.items:
            out += child.moduli()
        return out

    # ------------------------------------------------------------ семантика
    def holds_at(self, x, override=None):
        """Истинно ли выражение в точке x.

        ``override`` заменяет проверку листа ``m`` на готовое значение:
        ``{m: True}`` -- «ДЕЛ(x, m) истинно», ``{m: False}`` -- ложно.
        """
        if self.kind == "mod":
            m = self.items[0]
            if override is not None and m in override:
                return bool(override[m])
            return x % m == 0
        if self.kind == "and":
            return all(child.holds_at(x, override) for child in self.items)
        return any(child.holds_at(x, override) for child in self.items)

    def clause_lcms(self):
        """НОК всех конъюнктов ДНФ дерева, без дубликатов.

        Для листа -- сам модуль; для ``or`` -- объединение конъюнктов детей; для
        ``and`` -- все попарные НОК конъюнктов левой части с конъюнктами
        очередного ребёнка (дистрибутивность решётки делимости).
        """
        if self.kind == "mod":
            return (self.items[0],)
        if self.kind == "or":
            out = []
            for child in self.items:
                for value in child.clause_lcms():
                    if value not in out:
                        out.append(value)
            return tuple(out)
        acc = ()
        for child in self.items:
            values = child.clause_lcms()
            if not acc:
                acc = values
                continue
            nxt = []
            for u in acc:
                for v in values:
                    w = lcm(u, v)
                    if w not in nxt:
                        nxt.append(w)
            acc = tuple(nxt)
        return acc

    def answer_max(self):
        """Наибольшее A: «и» -> НОК, «или» -> НОД (то же, что НОД clause_lcms)."""
        if self.kind == "mod":
            return self.items[0]
        fn = lcm if self.kind == "and" else gcd
        out = self.items[0].answer_max()
        for child in self.items[1:]:
            out = fn(out, child.answer_max())
        return out

    def answer_min(self):
        """Наименьшее A: минимум по НОК конъюнктов ДНФ."""
        return min(self.clause_lcms())

    # ------------------------------------------------------------ описание
    def _describe_ops(self):
        """Запись операций дерева: НОК для «и», НОД для «или»."""
        if self.kind == "mod":
            return str(self.items[0])
        word = "НОК" if self.kind == "and" else "НОД"
        return "%s(%s)" % (word, ", ".join(c._describe_ops()
                                          for c in self.items))

    def describe(self, question):
        """Человекочитаемая запись операции для шага 2 в explain."""
        if question == "min_value":
            clauses = self.clause_lcms()
            if len(clauses) > 1:
                if self.kind == "or":
                    return "min(%s)" % ", ".join(
                        _lcm_word(child.clause_lcms()) for child in self.items)
                return "min(%s)" % ", ".join(str(v) for v in clauses)
        return self._describe_ops()

    # ------------------------------------------------------------ удаление листа
    def drop(self, target_m):
        """Новое дерево без листа target_m; None, если листьев не осталось."""
        if self.kind == "mod":
            return None if self.items[0] == target_m else self
        kept = []
        for child in self.items:
            new = child.drop(target_m)
            if new is not None:
                kept.append(new)
        if not kept:
            return None
        if len(kept) == 1:
            return kept[0]
        return _junction(self.kind, kept)


def _junction(kind, children):
    """Склеить детей одного вида и схлопнуть узел с единственным ребёнком."""
    flat = []
    for child in children:
        if isinstance(child, _DivExpr) and child.kind == kind:
            flat.extend(child.items)
        else:
            flat.append(child)
    if not flat:
        raise ValueError("_junction: пустой узел %r" % (kind,))
    if len(flat) == 1:
        return flat[0]
    return _DivExpr(kind, tuple(flat))


def _mod(m):
    """Лист ДЕЛ(x, m) как дерево делимости."""
    return _DivExpr("mod", (m,))


def _and(*children):
    """Узел «и» -- НОК детей (склеивается с такими же узлами)."""
    return _junction("and", children)


def _or(*children):
    """Узел «или» -- НОД детей (склеивается с такими же узлами)."""
    return _junction("or", children)


def _lcm_word(values):
    """НОК(...) по числам; одно число -- просто число."""
    values = tuple(values)
    if len(values) == 1:
        return str(values[0])
    return "НОК(%s)" % ", ".join(str(v) for v in values)


# ============================================================ проверка входа
def check_moduli(moduli):
    """Модули -> кортеж из 1..6 чисел, каждое в 2..999, без повторов."""
    if isinstance(moduli, int) and not isinstance(moduli, bool):
        moduli = (moduli,)
    try:
        mods = tuple(moduli)
    except TypeError:
        raise ValueError("moduli: ожидается число или кортеж чисел, получено %r"
                         % (moduli,)) from None
    if not 1 <= len(mods) <= MAX_MODULI:
        raise ValueError("moduli: нужно от 1 до %d модулей (a..f), получено %d"
                         % (MAX_MODULI, len(mods)))
    for m in mods:
        if isinstance(m, bool) or not isinstance(m, int):
            raise ValueError("moduli: модуль должен быть целым числом, "
                             "получено %r" % (m,))
        if not MIN_MODULUS <= m <= MAX_MODULUS:
            raise ValueError("moduli: модуль вне диапазона %d..%d: %d"
                             % (MIN_MODULUS, MAX_MODULUS, m))
    if len(set(mods)) != len(mods):
        raise ValueError("moduli: модули должны различаться, получено %s"
                         % ", ".join(str(m) for m in mods))
    return mods


def _check_pair(mods, name):
    """Двухфактные схемы: нет делимости одного модуля на другой, НОК <= 2520."""
    a, b = mods
    if a % b == 0 or b % a == 0:
        raise ValueError(
            "схема %s: ни один модуль не должен делить другой (%d и %d)"
            % (name, a, b)
        )
    limit = lcm(a, b)
    if limit > MAX_LCM:
        raise ValueError("схема %s: НОК(%d, %d) = %d больше %d"
                         % (name, a, b, limit, MAX_LCM))
    if name == "D5" and gcd(a, b) == 1:
        raise ValueError("схема D5: НОД(%d, %d) = 1, ответ вырожден"
                         % (a, b))


def max_size(moduli):
    """Потолок size() для формулы с данным числом модулей.

    ``MAX_SIZE = 28`` рассчитан на ядро из двух модулей: каждый ДЕЛ-узел
    занимает в ``size()`` три узла (сам узел и два операнда), поэтому на каждый
    модуль сверх двух к пределу добавляется по три узла. Иначе многофактные
    схемы (3..6 модулей) не проходили бы проверку длины, хотя на атомном уровне
    формула остаётся короткой.
    """
    count = len(tuple(moduli))
    return MAX_SIZE + 3 * max(0, count - 2)


@dataclass(frozen=True)
class _MultiDivScheme:
    """Схема для 3..6 модулей: дерево делимости, вопрос и ярус значимости.

    Интерфейс совместим с ``_Scheme`` (``name``, ``question``) и повторяет
    интерфейс ``Scheme`` из ``logic_tasks``: ``form``, ``core(moduli)``,
    ``answer(moduli)``, ``Applicable(moduli)``, ``explain_analytic(...)``,
    ``probes(moduli)``. ``rank``: 0 -- Приоритет 1 (ответ меняется и при
    удалении модуля, и при замене модуля на True/False), 1 -- Приоритет 2
    (ответ меняется только при замене).
    """

    name: str
    question: str
    expr: _DivExpr
    rank: int

    @property
    def form(self):
        """Как ядро читает вопрос: expr → ДЕЛ(x, A) или ДЕЛ(x, A) → expr."""
        return "to_a" if self.question == "max_value" else "from_a"

    def core(self, moduli):
        """Ядро в ДЕЛ-узлах: дерево и ДЕЛ(x, A) по сторонам импликации."""
        if self.question == "max_value":
            return ("imp", self.expr.formula(), div_fact_a())
        return ("imp", div_fact_a(), self.expr.formula())

    def answer(self, moduli):
        """Аналитический ответ дерева: НОД конъюнктов или минимум по ним."""
        if self.question == "max_value":
            return self.expr.answer_max()
        return self.expr.answer_min()

    def Applicable(self, moduli):   # noqa: N802 -- имя из интерфейса Scheme
        """Применима ли схема: оракул на периоде и значимость каждого модуля."""
        return _div_matters(self.expr, self.question,
                            tuple(check_moduli(moduli))) is not None

    def explain_analytic(self, moduli, answer):
        """Шаг 2 решения: НОК по конъюнктам и запись операции над ними."""
        nums = ", ".join(str(v) for v in self.expr.clause_lcms())
        desc = self.expr.describe(self.question)
        if self.question == "max_value":
            return ("2. Значения НОК по конъюнктам посылки: %s; их НОД равен "
                    "%s = %d, значит наибольшее A равно %d."
                    % (nums, desc, answer, answer))
        return ("2. Значения НОК по конъюнктам следствия: %s; наименьшее A "
                "равно %s = %d." % (nums, desc, answer))

    def probes(self, moduli):
        """Точки-свидетели при A = ответ: НОК конъюнктов и сам ответ.

        Для «наибольшего» A число A + 1 не делит хотя бы одно из этих НОК,
        значит формула ложна в этой точке и ответ опровергается за O(1) проб,
        без перебора периода НОК(период, A + 1).
        """
        return tuple(self.expr.clause_lcms()) + (int(self.answer(moduli)),)


def _lcm_all(nums):
    """НОК всех чисел кортежа."""
    out = 1
    for n in nums:
        out = lcm(out, n)
    return out


def _multiples_mask(m, period):
    """Маска точек 1..period, кратных m (бит x - 1 соответствует точке x)."""
    bits = ["1" if x % m == 0 else "0" for x in range(1, period + 1)]
    return int("".join(reversed(bits)), 2) if bits else 0


@lru_cache(maxsize=32)
def _period_table(mods):
    """(период, маска всех точек, {модуль: маска точек}) или None.

    Точка x из 1..период -- бит (x - 1). Множества истинности считаются
    битовыми операциями: перебор 10080 точек на каждую из сотен схем был бы
    слишком дорог. None -- период больше MAX_MULTI_PERIOD.
    """
    period = _lcm_all(mods)
    if period > MAX_MULTI_PERIOD:
        return None
    full = (1 << period) - 1
    table = {m: _multiples_mask(m, period) for m in mods}
    return period, full, table


def _mask(expr, table, full, override=None):
    """Маска истинности дерева на периоде; override заменяет лист на True/False."""
    if expr.kind == "mod":
        m = expr.items[0]
        if override is not None and m in override:
            return full if override[m] else 0
        return table[m]
    if expr.kind == "and":
        out = full
        for child in expr.items:
            out &= _mask(child, table, full, override)
        return out
    out = 0
    for child in expr.items:
        out |= _mask(child, table, full, override)
    return out


def _mask_answer(mask, question, period):
    """Крайний ответ по маске истинности: НОД всех точек или первая точка."""
    if not mask:
        return None
    if question == "min_value":
        return (mask & -mask).bit_length()
    out = 0
    for i in range(period):
        if mask >> i & 1:
            out = gcd(out, i + 1)
    return out


def _multi_moduli_ok(moduli):
    """Модули многофактной схемы: без повторов и без делимости одного на другой.

    Делимость одного модуля на другой -- то же вырождение, что у пары
    (``_check_pair``): меньший модуль ничего не добавляет (2, 4, 8 -- все три
    условия про одно и то же), поэтому такие наборы не годятся.
    """
    for i, a in enumerate(moduli):
        for b in moduli[i + 1:]:
            if a % b == 0 or b % a == 0:
                return False
    return True


def _div_matters(expr, question, moduli):
    """Универсальный оракул и значимость каждого модуля.

    -> 0 (Приоритет 1), 1 (Приоритет 2) или None (схема неприменима).

    Обязательны: без повторов и делимости модулей, период НОК(moduli) не больше
    MAX_MULTI_PERIOD, множество истинности на периоде непусто и не равно всем
    точкам, аналитический ответ не меньше MIN_MULTI_ANSWER и совпадает с
    оракулом, и каждый модуль виден -- хотя бы одна из замен листа на True/False
    меняет множество истинности.

    Приоритет 1 (строгий) требует от каждого модуля большего: обе замены меняют
    множество истинности, удаление модуля из дерева меняет ответ, и хотя бы одна
    из замен меняет ответ. Приоритет 2 (резервный) -- чтобы ответ меняла хотя бы
    одна замена.

    Почему обязательная неизбыточность -- «хотя бы одна замена», а не «обе»:
    для тройки (6, 10, 15) обе замены одновременно невозможны ни в одном дереве.
    Если f(∅) = 0 и f от каждой одиночной переменной истинна, монотонность даёт
    f = A ∨ B ∨ C, а тогда наибольший ответ равен НОД(6, 10, 15) = 1, то есть
    вырожден. Значит строгое «обе замены» оставлено признаком Приоритета 1, а
    обязательным -- что модуль вообще виден на периоде.
    """
    moduli = tuple(moduli)
    if not _multi_moduli_ok(moduli):
        return None
    table_info = _period_table(moduli)
    if table_info is None:
        return None
    period, full, table = table_info
    base = _mask(expr, table, full)
    if not base or base == full:
        return None
    answer = _mask_answer(base, question, period)
    if answer is None or answer < MIN_MULTI_ANSWER:
        return None
    analytic = (expr.answer_max() if question == "max_value"
                else expr.answer_min())
    if analytic != answer:
        return None
    strict, backup = True, True
    for m in moduli:
        mask_true = _mask(expr, table, full, {m: True})
        mask_false = _mask(expr, table, full, {m: False})
        if mask_true == base and mask_false == base:
            return None                 # модуль не виден на периоде
        both = mask_true != base and mask_false != base
        changed = (_mask_answer(mask_true, question, period) != answer
                   or _mask_answer(mask_false, question, period) != answer)
        dropped = expr.drop(m)
        dropped_answer = (None if dropped is None
                          else _mask_answer(_mask(dropped, table, full),
                                            question, period))
        if not both or not changed or dropped_answer == answer:
            strict = False
        if not changed:
            backup = False
    if strict:
        return 0
    if backup:
        return 1
    return None


def _pairs(seq):
    """Пары (seq[0],seq[1]), (seq[2],seq[3]), ...; при нечётном k -- ещё (seq[-2],seq[-1])."""
    out = [(seq[i], seq[i + 1]) for i in range(0, len(seq) - 1, 2)]
    if len(seq) % 2:
        out.append((seq[-2], seq[-1]))
    return out


def _half_variants(part):
    """Деревья на части seq: один на 1 модуль, два на 2, шесть на 3."""
    mods = [_mod(m) for m in part]
    if len(mods) == 1:
        return [("m", mods[0])]
    if len(mods) == 2:
        return [("lcm", _and(*mods)), ("gcd", _or(*mods))]
    x, y, z = mods
    return [
        ("lcm", _and(x, y, z)),
        ("gcd", _or(x, y, z)),
        ("lcm_xy_gcd_z", _or(_and(x, y), z)),
        ("gcd_xy_lcm_z", _and(_or(x, y), z)),
        ("lcm_yz_gcd_x", _or(_and(y, z), x)),
        ("gcd_yz_lcm_x", _and(_or(y, z), x)),
    ]


def _multi_trees(seq):
    """Структурные деревья на всех модулях seq: [(тег, _DivExpr), ...].

    В каждом дереве участвуют все модули упорядочения ровно по одному разу:
    сквозные НОК и НОД, цепочки соседних пар, разбиение на пары,
    чётные/нечётные, выделение одного модуля против остальных и разбиение на
    половины с разными комбинациями верхних операций.
    """
    k = len(seq)
    mods = [_mod(m) for m in seq]
    trees = [
        ("all_lcm", _and(*mods)),
        ("all_gcd", _or(*mods)),
        ("chain_lcm_gcd",
         _or(*[_and(mods[i], mods[i + 1]) for i in range(k - 1)])),
        ("chain_gcd_lcm",
         _and(*[_or(mods[i], mods[i + 1]) for i in range(k - 1)])),
    ]
    pairs = _pairs(seq)
    if len(pairs) > 1:
        trees.append(("pair_lcm_gcd",
                      _or(*[_and(_mod(x), _mod(y)) for x, y in pairs])))
        trees.append(("pair_gcd_lcm",
                      _and(*[_or(_mod(x), _mod(y)) for x, y in pairs])))
    evens, odds = seq[0::2], seq[1::2]
    if len(evens) > 1 and len(odds) > 1:
        trees.append(("eo_lcm_gcd",
                      _or(_and(*[_mod(m) for m in evens]),
                          _and(*[_mod(m) for m in odds]))))
        trees.append(("eo_gcd_lcm",
                      _and(_or(*[_mod(m) for m in evens]),
                           _or(*[_mod(m) for m in odds]))))
    for i in range(k):
        rest = [_mod(m) for m in seq[:i] + seq[i + 1:]]
        trees.append(("isolate_lcm_gcd_%d" % i, _or(_and(*rest), mods[i])))
        trees.append(("isolate_gcd_lcm_%d" % i, _and(_or(*rest), mods[i])))
    left = _half_variants(seq[:k // 2])
    right = _half_variants(seq[k // 2:])
    for ltag, lexpr in left:
        for rtag, rexpr in right:
            trees.append(("split_%s_%s_lcm" % (ltag, rtag),
                          _and(lexpr, rexpr)))
            trees.append(("split_%s_%s_gcd" % (ltag, rtag),
                          _or(lexpr, rexpr)))
    return trees


def _multi_orderings(moduli):
    """Упорядочения модулей без дублей: исходное и отсортированное по возрастанию."""
    mods = tuple(moduli)
    ordered = tuple(sorted(mods))
    if ordered == mods:
        return [(mods, "")]
    return [(mods, ""), (ordered, "_sorted")]


def _multi_div_schemes(moduli):
    """Пул схем для 3..6 модулей: дерево + вопрос, прошедшие оракул и значимость.

    Пул зависит только от набора модулей, поэтому считается один раз на набор
    (``_multi_pool_cached``): сотни деревьев с битовыми масками на периоде -- не
    то, что стоит повторять на каждый вызов генератора.
    """
    mods = check_moduli(moduli)
    if len(mods) < 3:
        return ()
    return _multi_pool_cached(mods)


@lru_cache(maxsize=32)
def _multi_pool_cached(mods):
    """Пул многофактных схем по кортежу модулей."""
    if _period_table(mods) is None:
        return ()
    pool, seen = [], set()
    for seq, order_tag in _multi_orderings(mods):
        for tree_tag, expr in _multi_trees(seq):
            for question in QUESTIONS:
                if question == "min_value" and expr.kind == "or" and all(
                        child.kind == "mod" for child in expr.items):
                    continue        # чистый НОД всех модулей: ответ тривиален
                if (expr, question) in seen:
                    continue
                seen.add((expr, question))
                rank = _div_matters(expr, question, mods)
                if rank is None:
                    continue
                pool.append(_MultiDivScheme(
                    "M%d_%s%s_%s" % (len(mods), tree_tag, order_tag,
                                     "max" if question == "max_value"
                                     else "min"),
                    question, expr, rank,
                ))
    return tuple(pool)


def _multi_selection(pool):
    """Сначала схемы Приоритета 1; Приоритет 2 -- только пока их меньше предела."""
    strict = [sch for sch in pool if sch.rank == 0]
    if len(strict) >= MAX_ACTIVE_DIV_SPECS:
        return strict
    return strict + [sch for sch in pool if sch.rank == 1]


def applicable_schemes(moduli):
    """Схемы, применимые к данным модулям, без учёта вопроса."""
    mods = check_moduli(moduli)
    if len(mods) == 1:
        return ("D3", "D4")
    if len(mods) == 2:
        a, b = mods
        if a % b == 0 or b % a == 0 or lcm(a, b) > MAX_LCM:
            return ()
        return ("D1", "D2", "D5") if gcd(a, b) > 1 else ("D1", "D2")
    return tuple(sch.name for sch in _multi_selection(_multi_div_schemes(mods)))


def _select_schemes(mods, scheme, question):
    """Явная схема проверяется на совместимость, auto -- фильтруется вопросом."""
    if question is not None and question not in QUESTIONS:
        raise ValueError("question: допустимы %s, получено %r"
                         % (", ".join(QUESTIONS), question))
    if len(mods) >= 3:
        if scheme is not None:
            raise ValueError(
                "схема %s рассчитана на 1--2 модуля; для %d модулей схема "
                "выбирается автоматически" % (scheme, len(mods)))
        chosen = _multi_selection(_multi_div_schemes(mods))
        if question is not None:
            chosen = [sch for sch in chosen if sch.question == question]
            if not chosen:
                raise ValueError("для модулей %r нет применимой схемы с "
                                 "вопросом %s" % (mods, question))
        if not chosen:
            raise ValueError(
                "для модулей %r нет применимой схемы: период НОК должен быть "
                "не больше %d, а каждый модуль должен влиять на ответ"
                % (mods, MAX_MULTI_PERIOD))
        return chosen
    if scheme is not None:
        if scheme not in _SCHEMES:
            raise ValueError("scheme: допустимы %s, получено %r"
                             % (", ".join(SCHEME_NAMES), scheme))
        sch = _SCHEMES[scheme]
        if sch.two:
            if len(mods) != 2:
                raise ValueError("схема %s требует модули a и b, получено %r"
                                 % (scheme, mods))
            _check_pair(mods, scheme)
        elif len(mods) != 1:
            raise ValueError("схема %s: модуль b должен отсутствовать, "
                             "получено %r" % (scheme, mods))
        if question is not None and question != sch.question:
            raise ValueError("схема %s отвечает на %s, а не на %s"
                             % (scheme, sch.question, question))
        return [sch]
    names = applicable_schemes(mods)
    if question is not None:
        names = tuple(name for name in names
                      if _SCHEMES[name].question == question)
        if not names:
            raise ValueError("для модулей %r нет применимой схемы с вопросом %s"
                             % (mods, question))
    if not names:
        raise ValueError("для модулей %r нет применимой схемы: в двухфактных "
                         "схемах модули не должны делить друг друга, а НОК "
                         "должен быть не больше %d" % (mods, MAX_LCM))
    return [_SCHEMES[name] for name in names]


def check_topics(topics):
    """Темы задачи на делимость -- логические темы без битовых."""
    if not topics:
        raise ValueError("topics: нужна хотя бы одна тема")
    bad = [topic for topic in topics if topic not in DIV_TOPICS]
    if bad:
        raise ValueError("topics: недопустимы для задач на делимость: %s"
                         % ", ".join(bad))


# ============================================================ атомы для запутывания
def atom_map(moduli):
    """ДЕЛ-узел -> атом: ("in","D<модуль>") для модулей и ("in","DA") для A."""
    out = {}
    for m in check_moduli(moduli):
        out[div_fact(m)] = ("in", "D%d" % m)
    out[div_fact_a()] = ("in", ATOM_A)
    return out


#: Связки, которые закон логики может поставить над атомами.
_BOOL_OPS = ("and", "or", "imp", "eqv")


def to_atoms(f, amap):
    """Формула из ДЕЛ-узлов -> формула из атомов; посторонний узел -- ValueError."""
    k = f[0]
    if k == "div":
        if f not in amap:
            raise ValueError("неизвестный ДЕЛ-узел: %r" % (f,))
        return amap[f]
    if k == "not":
        return ("not", to_atoms(f[1], amap))
    if k in _BOOL_OPS:
        return (k, to_atoms(f[1], amap), to_atoms(f[2], amap))
    raise ValueError("в ядре ДЕЛ допустимы только ДЕЛ-узлы и логические "
                     "связки, получено %r" % (k,))


def from_atoms(g, rev):
    """Атомная формула -> формула из ДЕЛ-узлов; посторонний атом -- ValueError."""
    k = g[0]
    if k == "in":
        if g not in rev:
            raise ValueError("неизвестный атом в формуле запутывания: %r" % (g,))
        return rev[g]
    if k == "tf":
        return g
    if k == "not":
        return ("not", from_atoms(g[1], rev))
    if k in _BOOL_OPS:
        return (k, from_atoms(g[1], rev), from_atoms(g[2], rev))
    raise ValueError("в формуле запутывания появился узел %r; допустимы только "
                     "атомы, tf и логические связки" % (k,))


def _atom_lit(rnd, atoms):
    """Случайный атом карты, с вероятностью 0.5 -- под отрицанием."""
    atom = rnd.choice(atoms)
    return ("not", atom) if rnd.random() < 0.5 else atom


# ============================================================ семантика
def period(moduli, answer):
    """НОК всех числовых модулей ядра и A: шаг, на котором формула периодична."""
    p = 1
    for m in tuple(moduli) + (answer,):
        p = lcm(p, m)
    return p


def holds(final, moduli, answer):
    """Истинна ли final при A = answer для всех натуральных x."""
    if answer < MIN_ANSWER:
        return False
    return all(ev(final, {"x": x, "A": answer})
               for x in range(1, period(moduli, answer) + 1))


def _truth_mask(f, table, full, a_mask):
    """Маска истинности формулы от x на периоде: битовые операции вместо ev.

    ДЕЛ(x, m) -- готовая маска точек, кратных m; ДЕЛ(x, A) -- маска при
    заданном A; ``not``/``and``/``or``/``imp``/``eqv`` считаются над масками.
    Так проверка ответа на периоде до 10080 точек стоит один проход по узлам
    формулы, а не цикл ev по всем x.
    """
    k = f[0]
    if k == "div":
        arg = f[2]
        if arg[0] == "var":
            return a_mask
        return table[arg[1]]
    if k == "tf":
        return full if f[1] else 0
    if k == "not":
        return full ^ _truth_mask(f[1], table, full, a_mask)
    left = _truth_mask(f[1], table, full, a_mask)
    right = _truth_mask(f[2], table, full, a_mask)
    if k == "and":
        return left & right
    if k == "or":
        return left | right
    if k == "imp":
        return (full ^ left) | right
    if k == "eqv":
        return full ^ (left ^ right)
    raise ValueError("в формуле ответа ожидались ДЕЛ, tf и логические связки, "
                     "получено %r" % (k,))


def _holds_mask(final, moduli, answer):
    """holds(final, moduli, answer) битовыми масками (для многофактных схем)."""
    if answer < MIN_ANSWER:
        return False
    span = period(moduli, answer)
    full = (1 << span) - 1
    table = {m: _multiples_mask(m, span) for m in moduli}
    return _truth_mask(final, table, full,
                       _multiples_mask(answer, span)) == full


def _verify_answer(scheme, moduli, final, answer):
    """Ответ подтверждается определением, а не только аналитикой.

    max_value: среди делителей ответа нет большего допустимого A, а A + 1
    опровергается контрпримером: сначала структурированные точки (модули ядра и
    их НОК), затем полный период. Ложность в одной точке доказывает непригодность
    A + 1, истинность в одной точке не доказывает ничего. min_value: ответ
    подходит, а при A - 1 находится x, где формула ложна (первый такой x и есть
    контрпример). Структурированные точки -- экономия: полный период
    НОК(726, 727) потребовал бы сотни тысяч вызовов ev, и перебор включается,
    только когда все такие точки истинны. У многофактных схем к точкам
    добавляются ``scheme.probes(moduli)`` -- НОК конъюнктов ДНФ и сам ответ:
    A + 1 не делит хотя бы одно из них, поэтому ответ опровергается за O(1).
    """
    multi = isinstance(scheme, _MultiDivScheme)
    if scheme.question == "max_value":
        check = _holds_mask if multi else holds
        valid = [A for A in divisors(answer) if check(final, moduli, A)]
        if answer not in valid:
            return False, "формула ложна при A = %d" % answer
        best = max(valid)
        if best != answer:
            return False, "нашлось большее допустимое A = %d" % best
        A2 = answer + 1
        probes = tuple(moduli) + (period(moduli, MIN_ANSWER),)
        if multi:
            probes += scheme.probes(moduli)
        if any(not ev(final, {"x": x, "A": A2}) for x in probes):
            return True, ""
        if not check(final, moduli, A2):
            return True, ""
        return False, "A = %d тоже подходит" % A2
    if not (_holds_mask(final, moduli, answer) if multi
            else holds(final, moduli, answer)):
        return False, "формула ложна при A = %d" % answer
    if answer - 1 >= MIN_ANSWER:
        less = answer - 1
        for x in range(1, period(moduli, less) + 1):
            if not ev(final, {"x": x, "A": less}):
                return True, ""
        return False, "A = %d тоже подходит" % less
    return True, ""


def _witness(scheme, moduli, final, answer):
    """(A2, x), где формула уже ложна: A2 = A + 1 для max, A2 = A - 1 для min.

    None, если контрпример не нашёлся: строку про свидетеля тогда не добавляем,
    но задачу это не бракует.
    """
    A2 = answer + 1 if scheme.question == "max_value" else answer - 1
    if A2 < MIN_ANSWER:
        return None
    for x in range(1, period(moduli, A2) + 1):
        if not ev(final, {"x": x, "A": A2}):
            return (A2, x)
    return None


# ============================================================ задача и решение
PREAMBLE = ("Обозначим через ДЕЛ(n, m) утверждение «натуральное число n "
            "делится без остатка на натуральное число m».")
TAIL = ("тождественно истинна (то есть принимает значение 1 при любом "
        "натуральном значении переменной x)?")

#: Теоретико-числовой шаг решения; подставляются модули a, b, НОК l и НОД g.
REASON = {
    "D1": "2. Посылка «x делится на {a} и на {b}» равносильна «x делится на "
          "НОК({a}, {b}) = {l}». При x = {l} посылка истинна, значит A должно "
          "делить {l}; наибольшее такое A равно {l}.",
    "D2": "2. Посылка «x делится на A» должна влечь делимость x на {a} и на "
          "{b}, значит A должно быть кратно НОК({a}, {b}) = {l}; наименьшее "
          "такое A равно {l}.",
    "D3": "2. При x = {a} посылка «x делится на {a}» истинна, значит A должно "
          "делить {a}; наибольшее такое A равно {a}.",
    "D4": "2. Из делимости x на A должна следовать делимость x на {a} при "
          "любом x, значит A должно быть кратно {a}; наименьшее такое A "
          "равно {a}.",
    "D5": "2. Посылка верна при x = {a} и при x = {b}, значит A должно делить "
          "НОД({a}, {b}) = {g}; наибольшее такое A равно {g}.",
}


def _solution_lines(scheme, moduli, core, final, hist, answer, witness):
    """Решение: цепочка законов, шаг про НОК/НОД и свидетель неоптимальности."""
    lines = ["1. Упростим формулу законами логики:"]
    lines += chain_lines(final, hist)
    lines.append("   Получили формулу, равносильную исходной: %s." % show(core))
    if isinstance(scheme, _MultiDivScheme):
        lines.append(scheme.explain_analytic(moduli, answer))
    else:
        a = moduli[0]
        b = moduli[1] if len(moduli) > 1 else a
        lines.append(REASON[scheme.name].format(a=a, b=b, l=lcm(a, b),
                                                g=gcd(a, b)))
    lines.append("3. A = %d подходит: формула истинна при всех x от 1 до %d."
                 % (answer, period(moduli, answer)))
    if witness is not None:
        A2, x = witness
        word = ("наибольшее" if scheme.question == "max_value"
                else "наименьшее")
        lines.append("4. При A = %d формула ложна уже при x = %d, поэтому "
                     "A = %d — %s." % (A2, x, answer, word))
    return tuple(lines)


@dataclass
class DivTask:
    """Условие на делимость, ответ и решение.

    ``answers`` содержит ровно один вопрос схемы: у каждой схемы свой вопрос,
    поэтому ``available`` -- кортеж из одного имени. ``selected_question``
    выставляется генератором и может быть переопределён вызывающим.
    """

    moduli: tuple
    scheme: str
    final: tuple
    core: tuple
    hist: list
    steps: int
    topics: tuple
    schedule: list
    answers: dict
    available: tuple
    selected_question: str
    solution: tuple
    tex: bool = True
    witness: object = None

    def answer_for(self, question):
        """Ответ на вопрос по уже построенному условию."""
        if question not in self.answers:
            raise ValueError("question=%s недоступен; доступны: %s"
                             % (question, ", ".join(self.available)))
        return int(self.answers[question])

    def condition_for(self, question):
        """Текст условия с формулировкой выбранного вопроса."""
        self.answer_for(question)
        sep, pad = SEP[self.tex]
        return ("%s Для какого %s натурального числа A формула%s%s%s%s%s"
                % (PREAMBLE, QUESTION_WORD[question], sep, pad,
                   fmt_formula(self.final, self.tex), sep, TAIL))

    @property
    def condition(self):
        return self.condition_for(self.selected_question)

    @property
    def answer(self):
        return self.answer_for(self.selected_question)

    def solution_text(self):
        """Решение целиком, с ответом в последней строке."""
        return "\n".join(self.solution) + "\nОтвет: %d." % self.answer

    def explain(self):
        """Условие и решение одним текстом -- для демонстраций и отчётов."""
        return "%s\n%s" % (self.condition, self.solution_text())


# ============================================================ генератор
@dataclass
class _State:
    """Состояние одной живой схемы в раундах генерации."""

    scheme: object                  # _Scheme (1--2 модуля) или _MultiDivScheme
    moduli: tuple
    rnd: object
    atoms: tuple                    # атомы карты в порядке модулей и DA
    rev: dict                       # атом -> ДЕЛ-узел
    core: tuple                     # ядро в ДЕЛ-узлах
    core_atoms: tuple               # то же ядро в атомах
    core_leaves: frozenset          # атомы ядра: ни один не должен пропасть
    task: object = None
    why: str = ""
    tries: int = 0                  # безуспешных попыток запутывания


def _scheme_core(scheme, moduli):
    """Ядро схемы в ДЕЛ-узлах: у многофактной схемы оно строится по дереву."""
    if isinstance(scheme, _MultiDivScheme):
        return scheme.core(moduli)
    return scheme_core(scheme.name, moduli)


def _scheme_answer(scheme, moduli):
    """Аналитический ответ схемы: НОК/НОД/модуль или ответ дерева."""
    if isinstance(scheme, _MultiDivScheme):
        return scheme.answer(moduli)
    return scheme_answer(scheme.name, moduli)


def _try_candidate(state, topics, steps, tex):
    """Одна попытка схемы: расписание, атомное запутывание, проверка ответа."""
    rnd = state.rnd
    sched = pick_facts_schedule(rnd, steps, topics)
    ctx = Ctx(rnd, lambda rnd=rnd, atoms=state.atoms: _atom_lit(rnd, atoms))
    out, why = obfuscate(state.core_atoms, sched, ctx)
    if out is None:
        return None, why
    final_atoms, hist_atoms = out
    if len(hist_atoms) != steps:
        return None, "получилось не ровно steps преобразований"
    used = leaves(final_atoms)
    if ("in", ATOM_A) not in used:
        return None, "атом A выпал из формулы"
    lost = sorted(name for _, name in state.core_leaves - used)
    if lost:
        return None, "из формулы выпал атом: %s" % ", ".join(lost)
    try:
        final = from_atoms(final_atoms, state.rev)
        hist = [(law, from_atoms(before, state.rev),
                 from_atoms(after, state.rev))
                for law, before, after in hist_atoms]
    except ValueError as error:
        return None, str(error)
    limit = max_size(state.moduli)
    if size(final) > limit:
        return None, "формула длиннее %d узлов" % limit
    if has_repeat_operands(final) and "idempotency" not in topics:
        return None, "повтор операндов без темы idempotency"
    answer = _scheme_answer(state.scheme, state.moduli)
    ok, why = _verify_answer(state.scheme, state.moduli, final, answer)
    if not ok:
        return None, why
    witness = _witness(state.scheme, state.moduli, final, answer)
    lines = _solution_lines(state.scheme, state.moduli, state.core, final, hist,
                            answer, witness)
    return DivTask(
        moduli=state.moduli, scheme=state.scheme.name, final=final,
        core=state.core, hist=hist, steps=steps, topics=tuple(topics),
        schedule=sched, answers={state.scheme.question: answer},
        available=(state.scheme.question,),
        selected_question=state.scheme.question, solution=lines, tex=tex,
        witness=witness,
    ), None


def _build_candidates(mods, topics, steps, tex, seed, max_attempts, schemes):
    """Раунды по живым схемам при общем бюджете попыток.

    Одна попытка на схему за раунд, схема выбывает после первого успеха;
    неуспех одной схемы вызов не валит -- причина попадает в отчёт, остальные
    схемы продолжают работать. У каждой схемы свой random.Random(seed).

    Живых состояний не больше `MAX_ACTIVE_DIV_SPECS`: при 3..6 модулях пул схем
    даёт десятки деревьев, и перебирать их все после первых двадцати прошедших
    оракул незачем. Если хотя бы одна схема уже построила задачу, схема,
    сделавшая `fair_share` безуспешных попыток, выбывает -- иначе одна
    несовместимая с темой схема сожгла бы остаток бюджета. Пока ни одна задача
    не построена, бюджет расходуется как раньше, вплоть до max_attempts.
    """
    amap = atom_map(mods)
    rev = {atom: node for node, atom in amap.items()}
    states = []
    for sch in schemes:
        if len(states) >= MAX_ACTIVE_DIV_SPECS:
            break
        core = _scheme_core(sch, mods)
        core_atoms = to_atoms(core, amap)
        states.append(_State(
            scheme=sch, moduli=mods, rnd=random.Random(seed),
            atoms=tuple(amap.values()), rev=rev, core=core,
            core_atoms=core_atoms,
            core_leaves=frozenset(leaves(core_atoms)),
        ))
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
            task, why = _try_candidate(st, topics, steps, tex)
            if task is None:
                st.why = why
            else:
                st.task = task
    candidates = [st.task for st in states if st.task is not None]
    reasons = ["%s: %s" % (st.scheme.name, st.why or "бюджет исчерпан")
               for st in states if st.task is None]
    return candidates, reasons


def _default_topics(steps, seed):
    """Пул тем по умолчанию; если steps меньше пула -- случайное подмножество.

    ``pick_facts_schedule`` требует, чтобы каждая заданная тема встретилась хотя
    бы раз, поэтому тем в расписании не может быть больше steps.
    """
    pool = list(DEFAULT_TOPICS)
    if steps < len(pool):
        pool = random.Random(seed).sample(pool, max(MIN_STEPS, steps))
    return tuple(pool)


def build_div_task(moduli, topics=None, steps=3, seed=None, scheme=None,
                   question=None, tex=True, max_attempts=2000):
    """Построить задачу на делимость по модулям.

    ``moduli`` -- (a,) для D3/D4, (a, b) для D1/D2/D5 или кортеж из 3..6 чисел:
    тогда схема строится деревом НОК/НОД (см. ``_multi_div_schemes``), а
    ``scheme`` должен оставаться None. ``scheme=None`` означает auto: берутся
    все применимые схемы, ``question`` их фильтрует. ``steps`` -- точное число
    преобразований, не меньше числа тем. ``seed=None`` заменяется на 0, чтобы
    вызов без seed оставался воспроизводимым. При несовместимом входе --
    ValueError, при исчерпании бюджета -- BudgetError.
    """
    mods = check_moduli(moduli)
    if (isinstance(steps, bool) or not isinstance(steps, int)
            or not MIN_STEPS <= steps <= MAX_STEPS):
        raise ValueError("steps: ожидается целое от %d до %d, получено %r"
                         % (MIN_STEPS, MAX_STEPS, steps))
    seed = 0 if seed is None else seed
    topics = _default_topics(steps, seed) if topics is None else tuple(topics)
    check_topics(topics)
    if steps < len(topics):
        raise ValueError("steps=%d меньше числа явно заданных тем (%d)"
                         % (steps, len(topics)))
    schemes = _select_schemes(mods, scheme, question)
    candidates, reasons = _build_candidates(
        mods, topics, steps, tex, seed, max_attempts, schemes,
    )
    if not candidates:
        raise BudgetError(
            "не удалось построить условие по ДЕЛ за %d попыток: moduli=%r, "
            "topics=%s, steps=%s, seed=%r; причины по схемам: %s"
            % (max_attempts, mods, tuple(topics), steps, seed,
               "; ".join(reasons) if reasons else "нет применимых схем")
        )
    if question is not None:
        suitable = [task for task in candidates if question in task.answers]
        if not suitable:
            available = [name for task in candidates for name in task.available]
            raise ValueError("question=%s недоступен; доступны: %s"
                             % (question, ", ".join(available)))
        chosen = random.Random(seed).choice(suitable)
        chosen.selected_question = question
        return chosen
    return random.Random(seed).choice(candidates)
