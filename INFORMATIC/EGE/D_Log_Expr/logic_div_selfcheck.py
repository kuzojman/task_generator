"""Самопроверка задач на делимость (ЕГЭ №15, DEL-2).

В проекте нет тестовой инфраструктуры (pytest не используется), поэтому
проверки живут в одном запускаемом модуле.

Что проверяется:
  * ДЕЛ как узел ядра: ev/show/show_tex для ДЕЛ и ¬ДЕЛ, отсутствие "div" в
    INFIX и TEX_INFIX, size/leaves, counterexample по ДЕЛ-формулам (A = 0 в
    переборе envs не должен ронять ev);
  * оракул: для каждой применимой схемы ответ генератора сверяется с полным
    перебором A по определению (период = НОК(модули, A), НОК через math.gcd)
    и с аналитикой (НОК/НОД/модуль); для «наибольшее» дополнительно нужно,
    чтобы A + 1 уже не подходило;
  * эквивалентность: `counterexample(атомный final, атомный core) is None`;
  * применимость схем по конфигурациям: ожидание считается независимо, плюс
    печатается таблица «конфигурация x схема» и что выбирает auto;
  * вопрос задачи: схема отвечает ровно на тот вопрос, который задан;
  * API: a = 1, b у схемы D3, вопрос против схемы, неизвестный ключ, битовая
    тема, steps меньше числа тем -> ParamError; удачный вызов даёт ровно
    {"condition": str, "answer": int};
  * детерминизм: один seed -> одинаковые condition/answer/scheme и final;
  * бюджет: topics=("equivalence",) -> BudgetError, а не RuntimeError;
  * многофактные схемы (3..6 модулей, DIV-UNLIM): сборка build_div_task и
    task_divisibility, все k модулей в final, `counterexample(core, final) is
    None`, ответ против независимого перебора A на периоде НОК(moduli),
    `_div_matters` для каждого из k модулей, составные схемы вида
    НОК(НОД(6, 9), НОД(10, 15)) в пуле, негативные тесты API (пропуск ключа
    модуля, дубликат модуля, вырожденная тройка).

Запуск из корня проекта::

    python -m INFORMATIC.EGE.D_Log_Expr.logic_div_selfcheck

Запуск из этого каталога::

    python logic_div_selfcheck.py

Код возврата: 0 -- все проверки прошли, 1 -- есть падения.
"""
import math
import os
import sys
import time

try:
    from . import logic_api, logic_core, logic_div
except ImportError:  # прямой запуск файлом, без пакетного импорта
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import logic_api
    import logic_core
    import logic_div


#: Конфигурации модулей: имя -> moduli в формате build_div_task.
CONFIGS = (
    ("(6,4)", (6, 4)),
    ("(4,9)", (4, 9)),
    ("(2,4)", (2, 4)),
    ("(6,)", (6,)),
    ("(33,242)", (33, 242)),
)

#: Конфигурации, где допустим полный перебор A (НОК не больше 36).
ORACLE_CONFIGS = ("(6,4)", "(4,9)", "(6,)")

#: Конфигурация только для аналитики: полный перебор A стоил бы 726^2 проверок.
ANALYTIC_ONLY = ("(33,242)",)

#: Темы и steps для генератора: те же, что в примерах task_logic.
TOPICS = ("morgan", "implication")
STEPS = 3
#: Seeds, среди которых ищется удачная сборка.
SEEDS = (1, 2, 3, 7)
#: Бюджет попыток в проверках (полный MAX_ATTEMPTS здесь не нужен).
ATTEMPTS = 400


# ============================================================ независимый оракул
def _lcm(*nums):
    """НОК через math.gcd: независимо от logic_div.lcm."""
    out = 1
    for n in nums:
        out = out * n // math.gcd(out, n)
    return out


def _period(mods, A):
    """Период формулы по определению: НОК всех модулей ядра и A."""
    return _lcm(*(tuple(mods) + (A,)))


def _true_all(final, mods, A):
    """Истинна ли формула при A для всех x из 1..период."""
    return all(logic_core.ev(final, {"x": x, "A": A})
               for x in range(1, _period(mods, A) + 1))


def _valid(final, mods, upto):
    """Все допустимые A из 1..upto по определению (без НОК/НОД схемы)."""
    return [A for A in range(1, upto + 1) if _true_all(final, mods, A)]


def _divisors(n):
    """Делители n: независимо от logic_div.divisors."""
    return [d for d in range(1, n + 1) if n % d == 0]


#: Схема -> (вопрос, аналитический ответ); НОК и НОД считаются через math.gcd.
ANALYTIC = {
    "D1": ("max_value", lambda a, b=0: _lcm(a, b)),
    "D2": ("min_value", lambda a, b=0: _lcm(a, b)),
    "D3": ("max_value", lambda a, b=0: a),
    "D4": ("min_value", lambda a, b=0: a),
    "D5": ("max_value", lambda a, b=0: math.gcd(a, b)),
}


def _expected_schemes(mods):
    """Применимые схемы по числовым условиям, без logic_div."""
    if len(mods) == 1:
        return ("D3", "D4")
    a, b = mods
    if a % b == 0 or b % a == 0 or _lcm(a, b) > 2520:
        return ()
    return ("D1", "D2", "D5") if math.gcd(a, b) > 1 else ("D1", "D2")


def _build(mods, name=None, question=None, topics=TOPICS, steps=STEPS):
    """Первая удачная сборка по SEEDS -> (задача, None) | (None, ошибка)."""
    error = None
    for one in SEEDS:
        try:
            return logic_div.build_div_task(
                mods, topics, steps, one, scheme=name, question=question,
                max_attempts=ATTEMPTS,
            ), None
        except (logic_div.BudgetError, ValueError) as exc:
            error = exc
    return None, error


# ============================================================ блоки проверок
def core_cases():
    """ДЕЛ -- узел ядра: ev, show, show_tex, size, leaves, counterexample."""
    cases = []
    six = logic_div.div_fact(6)
    four = logic_div.div_fact(4)
    a = logic_div.div_fact_a()
    neg = ("not", six)
    cases.append(("ev: ДЕЛ(12, 6) = 1", logic_core.ev(six, {"x": 12}) is True))
    cases.append(("ev: ДЕЛ(13, 6) = 0", logic_core.ev(six, {"x": 13}) is False))
    cases.append(("ev: ДЕЛ(0, 6) = 1", logic_core.ev(six, {"x": 0}) is True))
    cases.append(("ev: ¬ДЕЛ(13, 6) = 1", logic_core.ev(neg, {"x": 13}) is True))
    cases.append(("ev: ДЕЛ(x, A) при x = 12, A = 4",
                  logic_core.ev(a, {"x": 12, "A": 4}) is True))
    cases.append(("ev: ДЕЛ(5, 0) = 0 (защита envs от m = 0)",
                  logic_core.ev(("div", ("var", "x"), ("c", 0)),
                                {"x": 5}) is False))
    cases.append(("show: %s" % logic_core.show(six),
                  logic_core.show(six) == "ДЕЛ(x, 6)"))
    cases.append(("show: %s" % logic_core.show(a),
                  logic_core.show(a) == "ДЕЛ(x, A)"))
    cases.append(("show: %s" % logic_core.show(neg),
                  logic_core.show(neg) == "¬(ДЕЛ(x, 6))"))
    cases.append(("show: %s" % logic_core.show(("imp", six, a)),
                  logic_core.show(("imp", six, a))
                  == "(ДЕЛ(x, 6)) → (ДЕЛ(x, A))"))
    cases.append(("show_tex: %s" % logic_core.show_tex(six),
                  logic_core.show_tex(six) == r"\text{ДЕЛ}(x, 6)"))
    cases.append(("show_tex: %s" % logic_core.show_tex(neg),
                  logic_core.show_tex(neg) == r"\neg (\text{ДЕЛ}(x, 6))"))
    cases.append(("div нет в INFIX/TEX_INFIX",
                  "div" not in logic_core.INFIX
                  and "div" not in logic_core.TEX_INFIX))
    cases.append(("TYPE['div'] == 'bool'", logic_core.TYPE.get("div") == "bool"))
    cases.append(("size(ДЕЛ) = 3", logic_core.size(six) == 3))
    cases.append(("leaves(ДЕЛ(x, 6)) = {('var','x')}",
                  logic_core.leaves(six) == {("var", "x")}))
    cases.append(("counterexample(ДЕЛ(x,6), ДЕЛ(x,6)) is None",
                  logic_core.counterexample(six, six) is None))
    cases.append(("counterexample(ДЕЛ(x,4), ДЕЛ(x,6)) не None",
                  logic_core.counterexample(four, six) is not None))
    return cases


def oracle_cases(configs=CONFIGS, names=ORACLE_CONFIGS):
    """Ответ генератора против полного перебора A и против аналитики."""
    cases = []
    for title, mods in configs:
        if title not in names:
            continue
        for name in _expected_schemes(mods):
            question, analytic = ANALYTIC[name]
            task, error = _build(mods, name=name)
            if task is None:
                cases.append(("%s, %s: генератор не построил условие (%s)"
                              % (title, name, error), False))
                continue
            expected = analytic(*mods)
            valid = _valid(task.final, mods, expected)
            if question == "max_value":
                okey = (bool(valid) and max(valid) == expected
                        and not _true_all(task.final, mods, expected + 1))
                extreme = max(valid) if valid else None
            else:
                okey = bool(valid) and min(valid) == expected
                extreme = min(valid) if valid else None
            got = task.answer
            cases.append((
                "%s, %s, %s: генератор %d, аналитика %d, крайнее по перебору %s"
                % (title, name, question, got, expected, extreme),
                got == expected and okey,
            ))
    return cases


def equivalence_cases(configs=CONFIGS):
    """`counterexample(атомный final, атомный core) is None` для кандидатов."""
    cases = []
    for title, mods in configs:
        for name in _expected_schemes(mods):
            task, error = _build(mods, name=name)
            if task is None:
                cases.append(("%s, %s: генератор не построил условие (%s)"
                              % (title, name, error), False))
                continue
            try:
                amap = logic_div.atom_map(mods)
                final_atoms = logic_div.to_atoms(task.final, amap)
                core_atoms = logic_div.to_atoms(task.core, amap)
            except ValueError as exc:
                cases.append(("%s, %s: формула не переводится в атомы (%s)"
                              % (title, name, exc), False))
                continue
            bad = logic_core.counterexample(final_atoms, core_atoms)
            cases.append((
                "%s, %s: атомов %d, counterexample %s"
                % (title, name, len(logic_core.leaves(final_atoms)), bad),
                bad is None,
            ))
    return cases


def applicability_cases(configs=CONFIGS):
    """Применимость схем и выбор auto: -> (проверки, строки таблицы)."""
    cases, rows = [], []
    for title, mods in configs:
        expect = _expected_schemes(mods)
        got = logic_div.applicable_schemes(mods)
        cases.append(("%s: применимы %s, ожидалось %s"
                      % (title, ",".join(got) or "-", ",".join(expect) or "-"),
                      got == expect))
        cells = {}
        for name in logic_div.SCHEME_NAMES:
            try:
                logic_div.build_div_task(mods, TOPICS, STEPS, 1, scheme=name,
                                         max_attempts=1)
                cells[name] = "да"
            except logic_div.BudgetError:
                cells[name] = "да"      # схема применима, бюджета не хватило
            except ValueError:
                cells[name] = "-"
            want = "да" if name in expect else "-"
            if cells[name] != want:
                cases.append(("%s, %s: сборка говорит %s, ожидалось %s"
                              % (title, name, cells[name], want), False))
        auto = "нет"
        task, error = _build(mods)
        if expect:
            ok = task is not None and task.scheme in expect
            auto = task.scheme if task is not None else "нет (%s)" % error
            cases.append(("%s: auto выбрала %s из %s"
                          % (title, auto, ",".join(expect)), ok))
        else:
            cases.append(("%s: auto без применимых схем даёт ошибку входа"
                          % title,
                          task is None and isinstance(error, ValueError)))
        rows.append((title, cells, ",".join(expect) or "-", auto))
    return cases, rows


def question_cases(configs=CONFIGS):
    """Вопрос задачи: схема отвечает именно на него, ответ -- аналитический."""
    cases = []
    for title, mods in configs:
        expect = _expected_schemes(mods)
        for question in logic_div.QUESTIONS:
            wanted = [name for name in expect if ANALYTIC[name][0] == question]
            if not wanted:
                continue
            task, error = _build(mods, question=question)
            if task is None:
                cases.append(("%s, %s: генератор не построил условие (%s)"
                              % (title, question, error), False))
                continue
            expected = ANALYTIC[task.scheme][1](*mods)
            cases.append((
                "%s, %s: схема %s из %s, ответ %d, аналитика %d"
                % (title, question, task.scheme, ",".join(wanted),
                   task.answer, expected),
                task.scheme in wanted and task.selected_question == question
                and task.answer == expected,
            ))
    return cases


def analytic_cases(configs=CONFIGS, names=ANALYTIC_ONLY):
    """(33,242): только аналитика против делителей и кратных.

    Полный перебор всех A (726 вариантов по периоду до 726) не нужен: для
    «наибольшее» достаточно проверить все делители НОК и то, что A + 1 уже не
    подходит; для «наименьшее» -- что НОК подходит, а A - 1 нет.
    """
    cases = []
    for title, mods in configs:
        if title not in names:
            continue
        for name in _expected_schemes(mods):
            question, analytic = ANALYTIC[name]
            task, error = _build(mods, name=name)
            if task is None:
                cases.append(("%s, %s: генератор не построил условие (%s)"
                              % (title, name, error), False))
                continue
            expected = analytic(*mods)
            if question == "max_value":
                broken = [d for d in _divisors(expected)
                          if not _true_all(task.final, mods, d)]
                okey = (not broken
                        and not logic_core.ev(task.final,
                                              {"x": _lcm(*mods),
                                               "A": expected + 1}))
                detail = "делителей %d, сломанных %d" % (
                    len(_divisors(expected)), len(broken))
            else:
                less = expected - 1
                okey = (_true_all(task.final, mods, expected)
                        and not logic_core.ev(task.final,
                                              {"x": less, "A": less}))
                detail = "A - 1 ложна при x = %d" % less
            got = task.answer
            cases.append((
                "%s, %s, %s: генератор %d, аналитика %d, %s"
                % (title, name, question, got, expected, detail),
                got == expected and okey,
            ))
    return cases


# ============================================================ API и детерминизм
def _proto(mods, topics=TOPICS, steps=STEPS, seed=1, scheme=None,
           question=None):
    """Prototype строкой в формате task_divisibility."""
    parts = ["a=%d" % mods[0]]
    if len(mods) > 1:
        parts.append("b=%d" % mods[1])
    if scheme is not None:
        parts.append("scheme=%s" % scheme)
    parts.append("topics=%s" % ",".join(topics))
    parts.append("steps=%d" % steps)
    parts.append("seed=%d" % seed)
    if question is not None:
        parts.append("question=%s" % question)
    return ";".join(parts)


def _expect_param_error(cases, title, prototype):
    """Ожидание ParamError на неверном prototype."""
    try:
        result = logic_api.task_divisibility(prototype)
    except logic_api.ParamError:
        cases.append(("%s: ParamError" % title, True))
    except Exception as error:
        cases.append(("%s: вместо ParamError %s: %s"
                      % (title, type(error).__name__, error), False))
    else:
        cases.append(("%s: ошибки не было, ответ %r" % (title, result), False))


def api_cases():
    """task_divisibility: формат ответа и ошибки входа."""
    cases = []
    try:
        result = logic_api.task_divisibility(_proto((6, 4)))
    except Exception as error:
        cases.append(("api (6,4): исключение %s: %s"
                      % (type(error).__name__, error), False))
    else:
        cases.append(("api (6,4): ключи %s" % sorted(result),
                      sorted(result) == ["answer", "condition"]))
        cases.append(("api (6,4): condition -- str, answer -- int",
                      isinstance(result["condition"], str)
                      and isinstance(result["answer"], int)))
        cases.append(("api (6,4): в условии есть ДЕЛ(",
                      "ДЕЛ(" in result["condition"]))
    try:
        result = logic_api.task_divisibility(
            _proto((6, 4), question="min_value"))
        cases.append(("api (6,4), min_value: ответ 12", result["answer"] == 12))
    except Exception as error:
        cases.append(("api (6,4), min_value: исключение %s: %s"
                      % (type(error).__name__, error), False))
    _expect_param_error(cases, "api a = 1", _proto((1, 4)))
    _expect_param_error(cases, "api a = 0",
                        "a=0;b=4;topics=morgan;steps=1;seed=1")
    _expect_param_error(cases, "api b = 1000",
                        "a=6;b=1000;topics=morgan;steps=1;seed=1")
    _expect_param_error(cases, "api схема D3 при заданном b",
                        _proto((6, 4), scheme="D3"))
    _expect_param_error(cases, "api схема D1 без b", _proto((6,), scheme="D1"))
    _expect_param_error(cases, "api вопрос против схемы",
                        _proto((6, 4), scheme="D1", question="min_value"))
    _expect_param_error(cases, "api неизвестный ключ", _proto((6, 4)) + ";zz=5")
    _expect_param_error(cases, "api повторный ключ", _proto((6, 4)) + ";a=8")
    _expect_param_error(cases, "api битовая тема",
                        "a=6;b=4;topics=bit_test;steps=1;seed=1")
    _expect_param_error(cases, "api steps меньше числа тем",
                        _proto((6, 4), topics=("morgan", "implication"),
                               steps=1))
    _expect_param_error(cases, "api нет обязательного topics",
                        "a=6;b=4;steps=3;seed=1")
    _expect_param_error(cases, "api steps = 0",
                        "a=6;b=4;topics=morgan;steps=0;seed=1")
    _expect_param_error(cases, "api steps = 9",
                        "a=6;b=4;topics=morgan;steps=9;seed=1")
    _expect_param_error(cases, "api scheme = D9", _proto((6, 4), scheme="D9"))
    _expect_param_error(cases, "api question = max",
                        _proto((6, 4), question="max"))
    _expect_param_error(cases, "api (2,4): модуль делит другой", _proto((2, 4)))
    _expect_param_error(cases, "api (3,7): у D5 НОД = 1",
                        _proto((3, 7), scheme="D5"))
    return cases


def determinism_cases(configs=CONFIGS[:2], seed=11):
    """Один seed -> одинаковые condition/answer/scheme и одинаковый final."""
    cases = []
    for title, mods in configs:
        proto = _proto(mods, seed=seed)
        try:
            first = logic_api.task_divisibility(proto)
            second = logic_api.task_divisibility(proto)
            task1 = logic_div.build_div_task(mods, TOPICS, STEPS, seed,
                                             max_attempts=ATTEMPTS)
            task2 = logic_div.build_div_task(mods, TOPICS, STEPS, seed,
                                             max_attempts=ATTEMPTS)
        except Exception as error:
            cases.append(("%s: исключение %s: %s"
                          % (title, type(error).__name__, error), False))
            continue
        same_api = first == second
        same_task = (task1.final == task2.final
                     and task1.scheme == task2.scheme
                     and task1.answers == task2.answers
                     and task1.selected_question == task2.selected_question)
        cases.append((
            "%s: condition/answer совпали %s, схема %s, final/answers совпали %s"
            % (title, same_api, task1.scheme, same_task),
            same_api and same_task))
    return cases


def budget_cases(max_attempts=4):
    """Тема equivalence не срабатывает на ДЕЛ-ядре, ждём BudgetError."""
    cases = []
    try:
        logic_div.build_div_task((6, 4), ("equivalence",), 1, 1,
                                 max_attempts=max_attempts)
    except logic_div.BudgetError as error:
        text = str(error)
        cases.append(("бюджет: BudgetError вместо RuntimeError: %s"
                      % " ".join(text.split())[:140], True))
        cases.append(("бюджет: в тексте есть число попыток и причины по схемам",
                      ("за %d попыток" % max_attempts) in text
                      and "причины по схемам" in text))
    except Exception as error:          # RuntimeError и любое другое падение
        cases.append(("бюджет: вместо BudgetError %s: %s"
                      % (type(error).__name__, error), False))
    else:
        cases.append(("бюджет: тема equivalence не дала BudgetError", False))
    return cases


# ============================================================ 3..6 модулей
#: Конфигурации многофактных схем: имя -> moduli (порядок важен для деревьев).
MULTI_CONFIGS = (
    ("(6,10,15)", (6, 10, 15)),
    ("(6,10,45)", (6, 10, 45)),
    ("(6,4,9)", (6, 4, 9)),
    ("(6,9,10,15)", (6, 9, 10, 15)),
    ("(6,10,14,15,21)", (6, 10, 14, 15, 21)),
    ("(6,10,14,15,21,35)", (6, 10, 14, 15, 21, 35)),
)

#: Бюджет попыток многофактной сборки: схем много, но каждая дешёвая.
MULTI_ATTEMPTS = 600


def _multi_pool(mods):
    """Пул многофактных схем по модулям: имя -> схема."""
    return {sch.name: sch for sch in logic_div._multi_div_schemes(mods)}


def _multi_build(mods, question=None, steps=STEPS, topics=TOPICS):
    """Первая удачная многофактная сборка по SEEDS -> (задача, None) | (None, ошибка)."""
    error = None
    for one in SEEDS:
        try:
            return logic_div.build_div_task(
                mods, topics, steps, one, question=question,
                max_attempts=MULTI_ATTEMPTS,
            ), None
        except (logic_div.BudgetError, ValueError) as exc:
            error = exc
    return None, error


def _set_answer(values, question):
    """Крайний ответ по множеству истинности: НОД элементов или минимум."""
    values = tuple(values)
    if not values:
        return None
    if question == "min_value":
        return min(values)
    out = 0
    for v in values:
        out = math.gcd(out, v)
    return out


def _refute(final, mods, A):
    """Первое x, где формула при данном A ложна; None -- формула истинна везде."""
    for x in range(1, _period(mods, A) + 1):
        if not logic_core.ev(final, {"x": x, "A": A}):
            return x
    return None


def _multi_extreme(final, mods, answer, question):
    """Независимый перебор A на периоде -> (ok, пояснение).

    Для «наибольшего» A: сам A подходит, все его делители подходят, а каждое A
    из (A, НОК(moduli)] опровергается. Большее допустимое A обязано было бы
    найтись уже там: если A не делит НОК хотя бы одного конъюнкта, то в этой
    точке формула ложна, а выше НОК(moduli) такого конъюнкта заведомо хватает.
    Для «наименьшего» A: сам A подходит, а каждое A из 1..A-1 опровергается.
    """
    period = _lcm(*mods)
    if not _true_all(final, mods, answer):
        return False, "A = %d не подходит" % answer
    if question == "max_value":
        broken = [d for d in _divisors(answer) if not _true_all(final, mods, d)]
        if broken:
            return False, "делитель A = %d не подходит" % broken[0]
        if answer >= period:
            return True, ("A = %d равно НОК(moduli), больших A на периоде нет"
                          % answer)
        alive = [A for A in range(answer + 1, period + 1)
                 if _refute(final, mods, A) is None]
        if alive:
            return False, "A = %d тоже подходит" % alive[0]
        return True, "A подходит, все A из %d..%d опровергнуты" % (
            answer + 1, period)
    alive = [A for A in range(1, answer) if _refute(final, mods, A) is None]
    if alive:
        return False, "A = %d тоже подходит" % alive[0]
    return True, "A подходит, все A из 1..%d опровергнуты" % (answer - 1)


def multi_pool_cases(configs=MULTI_CONFIGS):
    """Пул схем: он непуст, составные НОК/НОД находятся, ранги корректны."""
    cases = []
    for title, mods in configs:
        pool = logic_div._multi_div_schemes(mods)
        strict = [sch for sch in pool if sch.rank == 0]
        names = logic_div.applicable_schemes(mods)
        cases.append((
            "%s: схем %d, Приоритет 1 -- %d, applicable_schemes -- %d"
            % (title, len(pool), len(strict), len(names)),
            bool(pool) and bool(names)
            and set(names) <= {sch.name for sch in pool},
        ))
    four = (6, 9, 10, 15)
    found = {sch.expr.describe("max_value"): sch.answer(four)
             for sch in logic_div._multi_div_schemes(four)
             if sch.question == "max_value"}
    for text, answer in (("НОК(НОД(6, 9), НОД(10, 15))", 15),
                         ("НОД(НОК(6, 9), НОК(10, 15))", 6)):
        cases.append(("пул %r: %s = %d" % (four, text, answer),
                      found.get(text) == answer))
    return cases


def _multi_task_cases(title, mods, question):
    """Сборка и проверки одной многофактной конфигурации по вопросу."""
    cases = []
    task, error = _multi_build(mods, question=question)
    if task is None:
        cases.append(("%s, %s: генератор не построил условие (%s)"
                      % (title, question, error), False))
        return cases
    nodes = {node for _, node in logic_core.subterms(task.final)}
    got = [m for m in mods if ("c", m) in nodes]
    cases.append((
        "%s, %s: схема %s, ответ %d, модулей в final %d/%d, A в final -- %s"
        % (title, question, task.scheme, task.answer, len(got), len(mods),
           ("var", "A") in nodes),
        len(got) == len(mods) and ("var", "A") in nodes,
    ))
    amap = logic_div.atom_map(mods)
    bad = logic_core.counterexample(logic_div.to_atoms(task.core, amap),
                                    logic_div.to_atoms(task.final, amap))
    cases.append(("%s, %s: counterexample(core, final) по атомам = %s"
                  % (title, question, bad), bad is None))
    ok, detail = _multi_extreme(task.final, mods, task.answer, question)
    cases.append(("%s, %s: независимый перебор A -- %s"
                  % (title, question, detail), ok))
    pool = _multi_pool(mods)
    sch = pool.get(task.scheme)
    if sch is None:
        cases.append(("%s, %s: схема %s не из пула"
                      % (title, question, task.scheme), False))
        return cases
    period = _lcm(*mods)
    base = frozenset(x for x in range(1, period + 1) if sch.expr.holds_at(x))
    broken = []
    for m in mods:
        yes = frozenset(x for x in range(1, period + 1)
                        if sch.expr.holds_at(x, {m: True}))
        no = frozenset(x for x in range(1, period + 1)
                       if sch.expr.holds_at(x, {m: False}))
        if yes == base and no == base:
            broken.append("%d не виден" % m)
        elif (_set_answer(yes, question) == task.answer
              and _set_answer(no, question) == task.answer):
            broken.append("ответ не видит %d" % m)
    rank = logic_div._div_matters(sch.expr, question, mods)
    cases.append((
        "%s, %s: ранг %s, значимы все %d модулей%s"
        % (title, question, rank, len(mods),
           "" if not broken else " (%s)" % ", ".join(broken)),
        rank is not None and not broken,
    ))
    return cases


def multi_build_cases(configs=MULTI_CONFIGS):
    """build_div_task для 3..6 модулей по обоим вопросам."""
    cases = []
    for title, mods in configs:
        for question in logic_div.QUESTIONS:
            cases.extend(_multi_task_cases(title, mods, question))
    return cases


def _multi_proto(mods, question=None, seed=1):
    """Prototype task_divisibility для многофактной конфигурации."""
    parts = ["%s=%d" % (key, m)
             for key, m in zip(logic_api.DIV_MODULUS_KEYS, mods)]
    parts.append("topics=%s" % ",".join(TOPICS))
    parts.append("steps=%d" % STEPS)
    parts.append("seed=%d" % seed)
    if question is not None:
        parts.append("question=%s" % question)
    return ";".join(parts)


def multi_api_cases(configs=MULTI_CONFIGS):
    """task_divisibility на 3..6 модулях: формат ответа и оба вопроса."""
    cases = []
    for title, mods in configs:
        for question in logic_div.QUESTIONS:
            try:
                result = logic_api.task_divisibility(
                    _multi_proto(mods, question=question))
            except Exception as error:
                cases.append(("%s, %s: api исключение %s: %s"
                              % (title, question, type(error).__name__, error),
                              False))
                continue
            ok = (sorted(result) == ["answer", "condition"]
                  and isinstance(result["condition"], str)
                  and isinstance(result["answer"], int)
                  and "ДЕЛ(" in result["condition"])
            cases.append(("%s, %s: api ответ %d, ключи %s"
                          % (title, question, result.get("answer"),
                             sorted(result)), ok))
    return cases


def multi_input_cases():
    """Негативные тесты API: пропуск модуля, дубликат, вырожденная тройка."""
    cases = []
    _expect_param_error(cases, "api 3 модуля без b (a и c)",
                        "a=6;c=10;topics=morgan,implication;steps=3;seed=1")
    _expect_param_error(cases, "api дубликат модуля (a и b)",
                        "a=6;b=6;topics=morgan,implication;steps=3;seed=1")
    _expect_param_error(cases, "api вырожденная тройка (2,4,8)",
                        "a=2;b=4;c=8;topics=morgan,implication;steps=3;seed=1")
    _expect_param_error(cases, "api лишний седьмой модуль (g)",
                        "a=6;b=10;c=14;d=15;e=21;f=35;g=77;"
                        "topics=morgan,implication;steps=3;seed=1")
    _expect_param_error(cases, "api модуль f вне диапазона",
                        "a=6;b=10;c=14;d=15;e=21;f=1000;"
                        "topics=morgan,implication;steps=3;seed=1")
    cases.append(("api: DIV_MODULUS_KEYS = a..f",
                  logic_api.DIV_MODULUS_KEYS
                  == ("a", "b", "c", "d", "e", "f")))
    cases.append(("модулей не больше %d" % logic_div.MAX_MODULI,
                  logic_div.MAX_MODULI == len(logic_api.DIV_MODULUS_KEYS)))
    return cases


def print_table(rows):
    """Таблица «конфигурация | D1..D5 | применимы | auto»."""
    print("\n=== применимость схем по конфигурациям ===")
    print("%-10s %-4s %-4s %-4s %-4s %-4s %-14s %s"
          % ("модули", "D1", "D2", "D3", "D4", "D5", "применимы", "auto"))
    for title, cells, expect, auto in rows:
        print("%-10s %-4s %-4s %-4s %-4s %-4s %-14s %s"
              % (title, cells["D1"], cells["D2"], cells["D3"], cells["D4"],
                 cells["D5"], expect, auto))


def run(cases, title):
    """Печатает таблицу проверок и возвращает число падений."""
    failures = 0
    print("\n=== %s ===" % title)
    for description, passed in cases:
        status = "ok  " if passed else "FAIL"
        print("  [%s] %s" % (status, description))
        if not passed:
            failures += 1
    print("  --- всего: %d, провалено: %d" % (len(cases), failures))
    return failures


def main():
    """Запускает все блоки самопроверки задач на делимость."""
    started = time.time()
    print("logic_div_selfcheck: схем %d, конфигураций %d, темы %s, steps %d"
          % (len(logic_div.SCHEME_NAMES), len(CONFIGS), ",".join(TOPICS),
             STEPS))
    failures = 0
    failures += run(core_cases(), "ядро: ДЕЛ как узел (ev, show, show_tex)")
    failures += run(oracle_cases(), "оракул: полный перебор A и аналитика")
    failures += run(analytic_cases(), "аналитика: (33,242) по делителям")
    failures += run(equivalence_cases(), "эквивалентность: counterexample(атомы)")
    availability, rows = applicability_cases()
    failures += run(availability, "применимость схем по конфигурациям")
    print_table(rows)
    failures += run(question_cases(), "вопрос задачи: схема и ответ")
    failures += run(api_cases(), "API: разбор prototype и ошибки входа")
    failures += run(determinism_cases(), "детерминизм по seed")
    failures += run(budget_cases(), "бюджет: BudgetError вместо RuntimeError")
    failures += run(multi_pool_cases(), "многофактные схемы: пул 3..6 модулей")
    failures += run(multi_build_cases(), "многофактные задачи: сборка и оракул")
    failures += run(multi_api_cases(), "многофактные задачи: task_divisibility")
    failures += run(multi_input_cases(), "многофактные задачи: ошибки входа")
    print("\nИтого провалов: %d, время: %.3f с"
          % (failures, time.time() - started))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
