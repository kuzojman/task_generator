"""Самопроверка facts-схем для задач на отрезках (ЕГЭ №15, SEG-2).

В проекте нет тестовой инфраструктуры (pytest не используется), поэтому
проверки живут в одном запускаемом модуле.

Что проверяется:
  * два оракула на независимом переборе отрезков A (концы из `L.pts` и
    середин между соседними концами, формула проверяется через `ev`):
    `oracle_solve` повторяет конвенцию solve (длина по границам множеств,
    сами концы A не проверяются) и сверяется с `solve`; `oracle_generator`
    повторяет конвенцию verify (A замкнут, проверяются все точки, включая
    концы) и сверяется с ответом генератора (`build_facts_task`);
  * расхождение оракулов: пары, где solve даёт длину, а verify вопрос не
    примет (открытый конец разности), печатаются отдельной таблицей;
  * эквивалентность: `counterexample(final, core) is None` для всех
    построенных кандидатов (не через `evaluate`);
  * регрессия legacy: `_facts_rule_specs` на равных, вложенных в обе стороны,
    частично пересекающихся, касающихся и раздельных отрезках даёт те же
    core/inner/outer, что и до правки, плюс `facts_constraints`/`facts_core`;
  * доступность вопросов по паре (схема, конфигурация): ожидание берётся из
    оракула, а не из зашитой таблицы;
  * многофактные схемы (SEG-3/UNLIM-2): для 3..6 фактов P..U пул
    `_multi_fact_schemes` содержит все факты в каждой схеме, в final входят все
    факты и A, verify проходит, `_matters` подтверждает значимость каждого
    факта, а `task_logic` с intervals=3..6 даёт тот же ответ, что
    `build_facts_task`;
  * побайтовая совместимость: формулы и множества плоских `_SetExpr` и
    `_pair_schemes`("P", "Q") совпадают с прежним `_SCHEMES`;
  * гибриды (SEG+ДЕЛ): для facts с делителями (a..f и синонимы D1..D6) в
    final входят все отрезки, все ДЕЛ(x, m) и A, ответ подтверждается
    `_verify_hybrid`, значимость каждого атома -- `_hybrid_matters`, а
    `task_logic` даёт тот же ответ; НОК(6, 4) = 12 в [10; 55] даёт 36;
  * границы входа: имена P..U и intervals 1..6 валидны, имя "Z" и intervals=7
    отсекаются;
  * детерминизм: один seed -> одинаковые condition/answer/scheme;
  * бюджет: заведомо невыполнимые topics -> BudgetError, а не RuntimeError.

Запуск из корня проекта::

    python -m INFORMATIC.EGE.D_Log_Expr.logic_facts_selfcheck

Запуск из этого каталога::

    python logic_facts_selfcheck.py

Код возврата: 0 -- все проверки прошли, 1 -- есть падения.
"""
import json
import os
import sys
import time

try:
    from . import logic_api, logic_core, logic_tasks
except ImportError:  # прямой запуск файлом, без пакетного импорта
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import logic_api
    import logic_core
    import logic_tasks


#: Конфигурации P/Q: имя -> facts в формате build_facts_task.
CONFIGS = (
    ("равны", {"P": (5, 10), "Q": (5, 10)}),
    ("P вложен в Q", {"P": (5, 10), "Q": (5, 20)}),
    ("Q вложен в P", {"P": (5, 20), "Q": (5, 10)}),
    ("Q строго внутри P", {"P": (5, 30), "Q": (12, 17)}),
    ("частичное пересечение", {"P": (5, 15), "Q": (10, 20)}),
    ("касание", {"P": (5, 10), "Q": (10, 20)}),
    ("раздельны", {"P": (5, 10), "Q": (20, 30)}),
    ("один факт", {"P": (5, 10)}),
)

#: Темы и steps для генератора: те же, что в документированном примере task_logic.
TOPICS = ("morgan", "implication")
STEPS = 3
#: Seeds, среди которых ищется удачная сборка для проверки с оракулом.
SEEDS = (1, 2, 3, 7)
#: Бюджет попыток в проверках (полный MAX_ATTEMPTS здесь не нужен).
ATTEMPTS = 400


def _holds(line, core, intervals, lo, hi, strict=False):
    """Истинна ли core на всём отрезке A=[lo; hi] при данных facts.

    Проверяются все контрольные точки: концы P/Q, концы A, середины между
    соседними контрольными точками и по точке слева/справа от всех pts.
    Между соседними контрольными точками истинность не меняется, поэтому
    такого набора точек достаточно.

    strict=False -- конвенция solve: сами концы A не проверяются, потому что
    solve считает длину по границам множеств и включённость концов в разности
    и дополнения не влияет на длину (Q − P для P=[5;10], Q=[10;20] имеет
    длину 10, хотя точка 10 в Q − P не входит).
    strict=True -- конвенция verify: A -- замкнутый отрезок, проверяются все
    точки, включая lo и hi.
    """
    xs = sorted(set(line.pts) | {lo, hi})
    checks = list(xs) + [(a + b) / 2.0 for a, b in zip(xs, xs[1:])]
    checks += [xs[0] - 1, xs[-1] + 1]
    for x in checks:
        if not strict and (x == lo or x == hi):
            continue
        env = {name: (a <= x <= b) for name, (a, b) in intervals.items()}
        env["A"] = lo <= x <= hi
        if not logic_core.ev(core, env):
            return False
    return True


def _grid(pts, quarters=False):
    """Сетка концов A: pts, середины соседних концов и (опционально) четверти."""
    grid = set(pts)
    for a, b in zip(pts, pts[1:]):
        grid.add((a + b) / 2.0)
        if quarters:
            grid.add((3 * a + b) / 4.0)
            grid.add((a + 3 * b) / 4.0)
    return sorted(grid)


def _best(line, intervals, core, want, ends, strict=False):
    """Лучшая длина A с концами из ends; None, если допустимых A нет."""
    best = None
    for lo in ends:
        for hi in ends:
            if hi <= lo or not _holds(line, core, intervals, lo, hi, strict):
                continue
            length = hi - lo
            if best is None or (length < best if want == "min" else length > best):
                best = length
    return best


def _width(line, S):
    """Длина выпуклой оболочки S по конвенции solve; None, если её нет."""
    if not S:
        return None
    lo, hi = line.bounds(min(S))[0], line.bounds(max(S))[1]
    if lo == -logic_core.INF or hi == logic_core.INF:
        return None
    return hi - lo


def _limit(line, intervals, core, want, strict):
    """Оптимум по сетке; None, если он улучшается на более дробной сетке.

    Более дробная сетка (четверти) ловит недостижимый оптимум: тогда можно
    взять A сколь угодно близко к границе промежутка, сам оптимум не
    достигается, и ни минимума, ни максимума нет.
    """
    best = _best(line, intervals, core, want, _grid(line.pts), strict)
    if best is None:
        return None
    fine = _best(line, intervals, core, want, _grid(line.pts, quarters=True),
                 strict)
    if fine is not None and ((want == "min" and fine < best)
                             or (want == "max" and fine > best)):
        return None
    return best


def oracle_solve(line, intervals, spec, want):
    """Длина, которую возвращает solve для пары (схема, вопрос).

    Конвенция solve: длина A считается по границам множеств, сами концы A в
    проверке не участвуют, а min требует положительной длины inner (A=[X; X]
    запрещён, поэтому точечный X отбрасывает только min_length).
    """
    if want == "min":
        width = _width(line, spec.inner)
        if width is None or width <= 0:
            return None
    return _limit(line, intervals, spec.core, want, strict=False)


def oracle_generator(line, intervals, spec, want):
    """Ответ, который реально примет verify, -- или None, если вопроса нет.

    Конвенция verify: A -- замкнутый отрезок, проверяются все контрольные
    точки, включая lo и hi. Замкнутый оптимум сравнивается с оптимумом solve:
    если он строго хуже, оптимум достигается только в пределе (открытый конец
    разности, например Q − P при касании P=[5;10], Q=[10;20]), и A, который
    построил solve, verify не примет.
    """
    strict = _limit(line, intervals, spec.core, want, strict=True)
    if strict is None:
        return None
    loose = oracle_solve(line, intervals, spec, want)
    if loose is None:
        return strict
    if (want == "min" and strict > loose) or (want == "max" and strict < loose):
        return None
    return strict


def _shape_ok(line, scheme, inner, outer):
    """Независимая проверка вырожденности по форме схемы (SEG-2-FIX, п.2).

    cover: схемы нет, если X пуст или из одной точки; inside: схемы нет, если
    в допустимом множестве нет цельного куска положительной длины; between и
    legacy i_subset_a_subset_u сохраняются: у точечного X теряется только
    min_length, это ловит оракул.
    """
    if scheme.form == "cover":
        width = _width(line, inner)
        return width is not None and width > 0
    if scheme.form == "inside":
        for run in line.runs(line.all - outer):
            width = _width(line, frozenset(run))
            if width is not None and width > 0:
                return True
        return False
    return True


def _spec_map(intervals):
    """{имя схемы: применимая схема} в порядке реестра."""
    _, specs = logic_tasks._scheme_specs(intervals)
    return {spec.name: spec for spec in specs}


def _same_answer(expected, got):
    """Сравнение ответа оракула (float) с целым ответом генератора."""
    if expected is None or got is None:
        return expected is None and got is None
    return float(got) == float(expected)


def oracle_cases(configs=CONFIGS):
    """oracle_solve против `solve` для всех применимых схем и вопросов."""
    cases = []
    for title, intervals in configs:
        line = logic_core.Line(dict(intervals))
        _, specs = logic_tasks._scheme_specs(intervals)
        for spec in specs:
            for question in spec.questions:
                want = dict(logic_tasks.FACT_QUESTIONS)[question]
                expected = oracle_solve(line, intervals, spec, want)
                res = logic_core.solve(line, spec.inner, spec.outer, want)
                got = None if res is None else res[0]
                cases.append((
                    "oracle_solve/solve: %s, %s, %s: оракул %s, solve %s"
                    % (title, spec.name, question, expected, got),
                    _same_answer(expected, got),
                ))
    return cases


def generator_cases(configs=CONFIGS, topics=TOPICS, steps=STEPS, seeds=SEEDS):
    """Ответ генератора совпадает с oracle_generator выбранной схемы."""
    cases = []
    for title, intervals in configs:
        line = logic_core.Line(dict(intervals))
        for question in ("min_length", "max_length"):
            task, error = None, None
            for seed in seeds:
                try:
                    task = logic_tasks.build_facts_task(
                        intervals, topics, steps, seed, question=question,
                        max_attempts=ATTEMPTS,
                    )
                    break
                except (logic_tasks.BudgetError, ValueError) as exc:
                    error = exc
            if task is None:
                cases.append(("%s, %s: генератор не построил условие (%s)"
                              % (title, question, error), False))
                continue
            spec = _spec_map(intervals).get(task.scheme)
            if spec is None:
                cases.append(("%s, %s: схема %r отсутствует в реестре"
                              % (title, question, task.scheme), False))
                continue
            want = dict(logic_tasks.FACT_QUESTIONS)[question]
            expected = oracle_generator(line, intervals, spec, want)
            got = task.answer_for(question)
            cases.append((
                "%s, %s: схема %s, ответ %s, оракул verify %s"
                % (title, question, task.scheme, got, expected),
                expected is not None and _same_answer(expected, got),
            ))
    return cases


def equivalence_cases(configs=CONFIGS, topics=TOPICS, steps=STEPS, seed=3):
    """`counterexample(final, core) is None` для всех построенных кандидатов."""
    cases = []
    for title, intervals in configs:
        try:
            candidates, reasons = logic_tasks._build_facts_candidates(
                intervals, topics, steps, seed, max_attempts=ATTEMPTS,
            )
        except Exception as error:      # падение генератора -- тоже провал
            cases.append(("%s: исключение %s: %s"
                          % (title, type(error).__name__, error), False))
            continue
        if not candidates:
            cases.append(("%s: нет кандидатов (%s)"
                          % (title, "; ".join(reasons)), False))
            continue
        bad = sorted(task.scheme for task in candidates
                     if logic_core.counterexample(task.final, task.core) is not None)
        cases.append((
            "%s: схем %d, неэквивалентных %d%s"
            % (title, len(candidates), len(bad),
               "" if not bad else " (" + ", ".join(bad) + ")"),
            not bad,
        ))
    return cases


def _legacy_expected(intervals):
    """Ожидаемые legacy-правила, собранные независимо от logic_tasks."""
    line = logic_core.Line(dict(intervals))
    order = tuple(intervals)
    sets = [line.atom[name] for name in order]
    inter = sets[0].intersection(*sets[1:])
    union = frozenset().union(*sets)

    def fold(op):
        node = ("in", order[0])
        for name in order[1:]:
            node = (op, node, ("in", name))
        return node

    a = ("in", "A")
    intersection_formula, union_formula = fold("and"), fold("or")
    expected = []
    if inter:
        expected.append((("and", ("imp", intersection_formula, a),
                          ("imp", a, union_formula)),
                         inter, line.all - union))
    expected.append((("imp", union_formula, a), union, frozenset()))
    return line, expected


def legacy_cases(configs=CONFIGS):
    """`_facts_rule_specs` и совместимые обёртки дают прежние core/inner/outer."""
    cases = []
    for title, intervals in configs:
        line, expected = _legacy_expected(intervals)
        got_line, got = logic_tasks._facts_rule_specs(intervals)
        ok = (got == expected and got_line.pts == line.pts
              and got_line.atom == line.atom)
        cases.append((
            "legacy %s: правил %d, ожидалось %d, specs совпали %s"
            % (title, len(got), len(expected), got == expected), ok))
        cline, inner, outer = logic_tasks.facts_constraints(intervals)
        cases.append((
            "legacy %s: facts_constraints/facts_core как specs[0]" % title,
            cline.pts == line.pts and inner == expected[0][1]
            and outer == expected[0][2]
            and logic_tasks.facts_core(intervals) == expected[0][0],
        ))
    return cases


def availability_cases(configs=CONFIGS):
    """Вопросы схемы против оракулов: -> (проверки, строки таблицы).

    Ожидание берётся не из зашитой таблицы, а считается независимо:
    вырожденность по форме (`_shape_ok`) плюс `oracle_solve`. Дополнительно
    проверяется, что вопросы, которые примет verify, не шире вопросов схемы.
    """
    cases, rows = [], []
    bad = 0
    for title, intervals in configs:
        line = logic_core.Line(dict(intervals))
        order = tuple(intervals)
        env = {name: line.atom[name] for name in order}
        mine = {spec.name: set(spec.questions)
                for spec in logic_tasks._scheme_specs(intervals)[1]}
        for scheme in logic_tasks._SCHEMES:
            solve_q, verify_q = set(), set()
            if scheme.legacy or len(order) > 1:
                inner, outer = scheme.constraints(env, order, line.all)
                if inner is not None and _shape_ok(line, scheme, inner, outer):
                    spec = logic_tasks._Spec(scheme, scheme.core(order), inner,
                                             outer, scheme.questions)
                    for question, want in logic_tasks.FACT_QUESTIONS:
                        if question not in scheme.questions:
                            continue
                        if oracle_solve(line, intervals, spec, want) is not None:
                            solve_q.add(question)
                        got_one = oracle_generator(line, intervals, spec, want)
                        if got_one is not None:
                            verify_q.add(question)
            got = mine.get(scheme.name, set())
            ok = got == solve_q and verify_q <= got
            bad += 0 if ok else 1
            if not ok:
                cases.append((
                    "%s, %s: схема %s, oracle_solve %s, verify %s"
                    % (title, scheme.name, sorted(got), sorted(solve_q),
                       sorted(verify_q)),
                    False))
            rows.append((title, scheme.name,
                         ",".join(sorted(solve_q)) or "-",
                         ",".join(sorted(got)) or "-",
                         ",".join(sorted(verify_q)) or "-", ok))
    cases.insert(0, (
        "доступность вопросов по (схема, конфигурация): расхождений %d" % bad,
        bad == 0))
    return cases, rows


def split_cases(configs=CONFIGS):
    """Пары, где solve даёт длину, а verify вопрос не примет.

    Ожидание не зашито: такое расхождение возможно только у inside-схемы на
    разности (открытый конец разности), поэтому любая другая схема с
    расхождением -- провал. Дополнительно требуется, чтобы у inside_diff_pq и
    inside_diff_qp такие пары были: иначе проверка ничего не проверяет.
    """
    cases, rows = [], []
    hits = {}
    for title, intervals in configs:
        line = logic_core.Line(dict(intervals))
        order = tuple(intervals)
        env = {name: line.atom[name] for name in order}
        for scheme in logic_tasks._SCHEMES:
            if not scheme.legacy and len(order) < 2:
                continue
            inner, outer = scheme.constraints(env, order, line.all)
            if inner is None or not _shape_ok(line, scheme, inner, outer):
                continue
            spec = logic_tasks._Spec(scheme, scheme.core(order), inner, outer,
                                     scheme.questions)
            for question, want in logic_tasks.FACT_QUESTIONS:
                if question not in scheme.questions:
                    continue
                solve_ans = oracle_solve(line, intervals, spec, want)
                if solve_ans is None:
                    continue
                if oracle_generator(line, intervals, spec, want) is not None:
                    continue
                rows.append((title, scheme.name, question, solve_ans))
                hits[scheme.name] = hits.get(scheme.name, 0) + 1
                if scheme.form != "inside" or scheme.x.kind != "diff":
                    cases.append((
                        "%s, %s, %s: solve %s, verify отказал у схемы без "
                        "открытого конца разности"
                        % (title, scheme.name, question, solve_ans), False))
    for name in ("inside_diff_pq", "inside_diff_qp"):
        cases.append(("%s: пар solve/verify %d" % (name, hits.get(name, 0)),
                      hits.get(name, 0) > 0))
    cases.insert(0, ("расхождений solve/verify: %d (ожидается хотя бы одно)"
                     % len(rows), bool(rows)))
    return cases, rows


def _prototype(intervals, seed, topics=TOPICS, steps=STEPS):
    """Prototype строкой, как у task_logic (facts -- компактный JSON)."""
    facts = {name: [lo, hi] for name, (lo, hi) in intervals.items()}
    return ("facts=%s;topics=%s;steps=%d;intervals=%d;seed=%d"
            % (json.dumps(facts, separators=(",", ":"), sort_keys=True),
               ",".join(topics), steps, len(intervals), seed))


def determinism_cases(configs=CONFIGS[:2], seed=11):
    """Один seed -> одинаковые condition/answer/scheme и одинаковый final."""
    cases = []
    for title, intervals in configs:
        proto = _prototype(intervals, seed)
        try:
            first = logic_api.task_logic(proto)
            second = logic_api.task_logic(proto)
            task1 = logic_tasks.build_facts_task(intervals, TOPICS, STEPS, seed)
            task2 = logic_tasks.build_facts_task(intervals, TOPICS, STEPS, seed)
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
            same_api and same_task and bool(task1.scheme)))
    return cases


def budget_cases(intervals=None, topics=("xor",), steps=1, seed=1,
                 max_attempts=4):
    """Тема xor бессмысленна на прямой: схема не соберётся, ждём BudgetError."""
    intervals = intervals or {"P": (5, 10), "Q": (10, 20)}
    cases = []
    try:
        logic_tasks.build_facts_task(intervals, topics, steps, seed,
                                     max_attempts=max_attempts)
    except logic_tasks.BudgetError as error:
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
        cases.append(("бюджет: невыполнимые topics не дали BudgetError", False))
    return cases


# ---------------------------------------------------------------- 3..6 фактов
#: Размеры многофактного блока: сколько отрезков-фактов в условии.
MULTI_SIZES = (3, 4, 5, 6)
#: Seeds для многофактных проверок: первый удачный seed останавливает поиск.
MULTI_SEEDS = (1, 2, 3, 7, 11)
#: Бюджет попыток на одну многофактную сборку (полный MAX_ATTEMPTS не нужен).
MULTI_ATTEMPTS = 200


def _geometry(kind, k):
    """facts для k фактов заданной геометрии.

    цепочка -- соседние отрезки пересекаются, крайние не пересекаются;
    острова -- первый факт служит контейнером, остальные лежат внутри него;
    мост -- два непересекающихся блока, промежуток между ними накрывает
    первый факт.
    """
    names = logic_tasks.FACT_NAMES[:k]
    if kind == "цепочка":
        return {name: (5 + 10 * i, 15 + 10 * i)
                for i, name in enumerate(names)}
    if kind == "острова":
        facts = {names[0]: (5, 50)}
        for i, name in enumerate(names[1:]):
            lo = 10 + 8 * i
            facts[name] = (lo, lo + 6)
        return facts
    facts = {names[0]: (10, 40)}                # мост через промежуток
    half = k // 2
    for i, name in enumerate(names[1:], start=1):
        if i <= half:
            facts[name] = (5 + 3 * i, 12 + 3 * i)               # левый блок
        else:
            facts[name] = (38 + 3 * (i - half), 45 + 3 * (i - half))
    return facts


def multi_configs(sizes=MULTI_SIZES):
    """[(название, facts)] по всем геометриям и размерам 3..6."""
    return [("k=%d, %s" % (k, kind), _geometry(kind, k))
            for k in sizes for kind in ("цепочка", "острова", "мост")]


def _expr_names(expr, order):
    """Имена фактов, входящих в дескриптор (пустой args = все факты order)."""
    items = expr.args if expr.args else tuple(order)
    out = set()
    for item in items:
        if isinstance(item, logic_tasks._SetExpr):
            out |= _expr_names(item, order)
        else:
            out.add(item)
    return out


def _find_spec(intervals, name, task, order):
    """`_Spec` задачи по имени схемы пула (inner/outer берутся у задачи)."""
    for scheme in logic_tasks._scheme_candidates(order, intervals):
        if scheme.name == name:
            return logic_tasks._Spec(scheme, scheme.core(order), task.inner,
                                     task.outer, scheme.questions)
    return None


def flat_setexpr_cases():
    """Плоские `_SetExpr` и `_pair_schemes`: формулы и множества прежние."""
    order = ("P", "Q")
    line = logic_core.Line({"P": (5, 15), "Q": (10, 20)})
    env = {name: line.atom[name] for name in order}
    p, q = frozenset(env["P"]), frozenset(env["Q"])
    setexpr = logic_tasks._SetExpr
    expected = (
        ("inter", setexpr("inter"), ("and", ("in", "P"), ("in", "Q")), p & q),
        ("union", setexpr("union"), ("or", ("in", "P"), ("in", "Q")), p | q),
        ("name", setexpr("name", ("P",)), ("in", "P"), p),
        ("diff", setexpr("diff", ("P", "Q")),
         ("and", ("in", "P"), ("not", ("in", "Q"))), p - q),
        ("symdiff", setexpr("symdiff", ("P", "Q")),
         ("or", ("and", ("in", "P"), ("not", ("in", "Q"))),
          ("and", ("not", ("in", "P")), ("in", "Q"))), p ^ q),
    )
    cases = []
    for title, expr, formula, points in expected:
        cases.append((
            "плоский %s: формула и множество прежние" % title,
            expr.formula(order) == formula
            and expr.evaluate(env, order) == points
            and expr.evaluate(env, order, line.pts) == points,
        ))
    cases.append(("_pair_schemes(P, Q) совпадает с _SCHEMES",
                  logic_tasks._pair_schemes("P", "Q") == logic_tasks._SCHEMES))
    return cases


def multi_pool_cases(sizes=MULTI_SIZES):
    """Пул 3..6: в каждой схеме все факты, базовые схемы на месте, имена разные."""
    cases = []
    for k in sizes:
        intervals = _geometry("цепочка", k)
        order = tuple(intervals)
        pool = logic_tasks._multi_fact_schemes(order, intervals)
        names = [scheme.name for scheme in pool]
        missing = []
        for scheme in pool:
            used = _expr_names(scheme.x, order)
            if scheme.y is not None:
                used |= _expr_names(scheme.y, order)
            if not set(order) <= used:
                missing.append(scheme.name)
        base_ok = all(name in names for name in logic_tasks._MULTI_BASE_NAMES)
        cases.append((
            "k=%d: схем %d, без факта %d, базовые %s, имена уникальны %s"
            % (k, len(pool), len(missing), base_ok,
               len(set(names)) == len(names)),
            not missing and base_ok and len(set(names)) == len(names)))
    return cases


def _facts_proto(seed, intervals, facts):
    """prototype task_logic с явными facts: dict либо список имён, либо число."""
    if isinstance(facts, int):
        names = logic_tasks.FACT_NAMES[:facts]
        facts = {name: (5 + 10 * i, 15 + 10 * i)
                 for i, name in enumerate(names)}
    elif isinstance(facts, (list, tuple)):
        facts = {name: (5 + 10 * i, 15 + 10 * i)
                 for i, name in enumerate(facts)}
    text = {name: [lo, hi] for name, (lo, hi) in facts.items()}
    return ("facts=%s;topics=%s;steps=%d;intervals=%d;seed=%d"
            % (json.dumps(text, separators=(",", ":")), ",".join(TOPICS),
               STEPS, intervals, seed))


def multi_build_cases(configs=None, seeds=MULTI_SEEDS, topics=TOPICS,
                      steps=STEPS, max_attempts=MULTI_ATTEMPTS):
    """3..6 фактов: сборка, состав final, verify и `_matters` по каждому факту."""
    cases = []
    for title, intervals in (configs if configs is not None
                             else multi_configs()):
        order = tuple(intervals)
        for question in ("min_length", "max_length"):
            want = dict(logic_tasks.FACT_QUESTIONS)[question]
            task, error = None, None
            for seed in seeds:
                try:
                    task = logic_tasks.build_facts_task(
                        intervals, topics, steps, seed, question=question,
                        max_attempts=max_attempts,
                    )
                    break
                except (logic_tasks.BudgetError, ValueError) as exc:
                    error = exc
            if task is None:
                cases.append(("%s, %s: генератор не построил условие (%s)"
                              % (title, question, error), False))
                continue
            line = task.line
            env = {name: line.atom[name] for name in order}
            used = logic_core.leaves(task.final)
            facts_in = [name for name in order if ("in", name) not in used]
            a_in = ("in", "A") in used
            res = logic_core.solve(line, task.inner, task.outer, want)
            verified = res is not None and logic_core.verify(
                line, lambda env_, final=task.final: logic_core.ev(final, env_),
                res[2], res[3])
            spec = _find_spec(intervals, task.scheme, task, order)
            matters = (spec is not None and res is not None
                       and logic_tasks._matters(line, env, order, spec,
                                                question, res[0]))
            answer_ok = res is not None and task.answer_for(question) == res[0]
            cases.append((
                "%s, %s: схема %s, фактов в final %d/%d, A %s, verify %s, "
                "_matters %s, ответ %s"
                % (title, question, task.scheme, len(order) - len(facts_in),
                   len(order), a_in, verified, matters,
                   task.answer_for(question)),
                not facts_in and a_in and verified and matters and answer_ok))
    return cases


def multi_api_cases(sizes=MULTI_SIZES, seeds=MULTI_SEEDS):
    """task_logic на intervals=3..6: ответ совпадает с build_facts_task."""
    cases = []
    for k in sizes:
        intervals = _geometry("цепочка", k)
        got, direct, seed_used, error = None, None, None, None
        for seed in seeds:
            try:
                got = logic_api.task_logic(_facts_proto(seed, k, k))
                direct = logic_tasks.build_facts_task(intervals, TOPICS, STEPS,
                                                      seed, tex=True)
                seed_used = seed
                break
            except Exception as exc:        # любое падение -- тоже провал
                got, error = None, exc
        if got is None:
            cases.append(("intervals=%d: task_logic не построил условие (%s)"
                          % (k, error), False))
            continue
        answer = got.get("answer") if isinstance(got, dict) else None
        cases.append((
            "intervals=%d, seed=%s: task_logic %s, ответ %s, "
            "build_facts_task %s"
            % (k, seed_used, sorted(got), answer, direct.answer),
            isinstance(got, dict) and set(got) == {"condition", "answer"}
            and isinstance(answer, int) and answer == direct.answer
            and "A" in got["condition"]))
    return cases


def multi_input_cases():
    """Границы входа: 3..6 фактов валидны, имя "Z" и intervals=7 отсекаются."""
    cases = []
    try:
        got = logic_api.task_logic(_facts_proto(1, 5, 5))
    except Exception as exc:
        cases.append(("intervals=5: %s: %s" % (type(exc).__name__, exc), False))
    else:
        cases.append(("intervals=5: задача построена, ответ %s"
                      % got.get("answer"),
                      isinstance(got, dict)
                      and set(got) == {"condition", "answer"}))
    for title, proto, needle in (
        ("intervals=7", _facts_proto(1, 7, 1), "от 1 до 6"),
        ("имя Z", _facts_proto(2, 2, ["P", "Z"]), "Z"),
    ):
        try:
            logic_api.task_logic(proto)
        except logic_api.ParamError as exc:
            cases.append(("%s: ParamError с %r" % (title, needle),
                          needle in str(exc)))
        except Exception as exc:            # не тот класс исключения
            cases.append(("%s: вместо ParamError %s: %s"
                          % (title, type(exc).__name__, exc), False))
        else:
            cases.append(("%s: вход не отсечён" % title, False))
    try:
        logic_tasks._facts_env({"P": (1, 2), "Z": (3, 4)})
    except ValueError as exc:
        cases.append(("_facts_env: имя Z отсечено, текст перечисляет P..U",
                      "P, Q, R, S, T, U" in str(exc)))
    except Exception as exc:
        cases.append(("_facts_env: вместо ValueError %s"
                      % type(exc).__name__, False))
    else:
        cases.append(("_facts_env: имя Z не отсечено", False))
    try:
        line, env, order = logic_tasks._facts_env(
            {"P": (1, 2), "R": (3, 4), "U": (5, 6)})
    except Exception as exc:
        cases.append(("_facts_env: имена R и U недопустимы (%s)" % exc, False))
    else:
        cases.append(("_facts_env: имена R и U допустимы",
                      order == ("P", "R", "U") and set(env) == set(order)
                      and bool(line.pts)))
    return cases


# ---------------------------------------------------------------- гибриды: отрезки + ДЕЛ
#: Гибридные конфигурации: (название, отрезки, модули, вопросы).
HYBRID_CONFIGS = (
    ("1+2: P, 6, 4", {"P": (10, 55)}, (6, 4),
     ("min_length", "max_length")),
    ("2+2: P, Q, 6, 4", {"P": (10, 55), "Q": (20, 80)}, (6, 4),
     ("min_length", "max_length", "max_value", "min_value")),
    ("3+3: P, Q, R, 6, 10, 15",
     {"P": (10, 60), "Q": (20, 50), "R": (30, 80)}, (6, 10, 15),
     ("min_length",)),
)
#: Способы назвать делители в facts: буквы a..f и синонимы D1..D6.
HYBRID_KEYS = ("letters", "div")

#: Модули для проверки НОК: НОК(6, 4) = 12, кратные 12 в [10; 55] -- 12..48.
LCM_INTERVALS = {"P": (10, 55)}
LCM_DIVISORS = {"a": 6, "b": 4}


def _hybrid_facts(intervals, moduli, kind):
    """facts с делителями под ключами a..f (letters) или D1..D6 (div)."""
    facts = {name: [lo, hi] for name, (lo, hi) in intervals.items()}
    names = (("a", "b", "c", "d", "e", "f") if kind == "letters"
             else logic_tasks.DIV_FACT_NAMES[:6])
    for key, modulus in zip(names, moduli):
        facts[key] = modulus
    return facts


def _hybrid_proto(facts, n_intervals, question, seed):
    """prototype task_logic: отрезки списками, делители -- числами."""
    return ("facts=%s;intervals=%d;question=%s;topics=%s;steps=%d;seed=%d"
            % (json.dumps(facts, separators=(",", ":")), n_intervals,
               question, ",".join(TOPICS), STEPS, seed))


def _hybrid_scheme(intervals, moduli, name):
    """Схема гибридного пула по имени (None, если такой схемы нет)."""
    divisors = dict(zip(logic_tasks.DIV_FACT_NAMES, moduli))
    for scheme in logic_tasks._hybrid_schemes(intervals, divisors):
        if scheme.name == name:
            return scheme
    return None


def hybrid_lcm_cases():
    """НОК(6, 4) = 12: кратные 12 в [10; 55] -- 12..48, min_length равен 36."""
    cases = []
    multiples = [x for x in range(LCM_INTERVALS["P"][0],
                                  LCM_INTERVALS["P"][1] + 1) if x % 12 == 0]
    cases.append((
        "кратные НОК(6, 4)=12 в [10; 55]: %d..%d, длина %d"
        % (multiples[0], multiples[-1], multiples[-1] - multiples[0]),
        multiples[0] == 12 and multiples[-1] == 48
        and multiples[-1] - multiples[0] == 36))
    moduli = tuple(LCM_DIVISORS.values())
    limit = LCM_INTERVALS["P"][1]
    for name, answer, place in (
        ("hyb_cover_name_lcm", 36, (12, 48)),
        ("hyb_avoid_name_lcm", 10, (13, 23)),
    ):
        scheme = _hybrid_scheme(LCM_INTERVALS, moduli, name)
        if scheme is None:
            cases.append(("схемы %s нет в гибридном пуле" % name, False))
            continue
        got = logic_tasks._hyb_plan(scheme, LCM_INTERVALS, moduli, limit)
        cases.append(("%s: ответ %s, A=%s (ожидалось %s, %s)"
                      % (name, got[0], got[1], answer, place),
                      got[0] == answer and got[1] == place))
    return cases


def hybrid_cases(configs=HYBRID_CONFIGS, seeds=MULTI_SEEDS, topics=TOPICS,
                 steps=STEPS, attempts=MULTI_ATTEMPTS):
    """Гибриды: ответ, состав final, значимость атомов и task_logic.

    Для каждой конфигурации, вопроса и способа назвать делители проверяется:
    сборка `build_facts_task`, ответ оракула схемы, вхождение в final всех
    отрезков, всех ДЕЛ(x, m) и A, `_hybrid_matters`, `_verify_hybrid` и
    совпадение ответа `task_logic` с ответом напрямую собранной задачи.
    """
    cases = []
    for title, intervals, moduli, questions in configs:
        limit = max(hi for _lo, hi in intervals.values())
        order = tuple(intervals)
        for question in questions:
            for kind in HYBRID_KEYS:
                facts = _hybrid_facts(intervals, moduli, kind)
                tag = "%s, %s, %s" % (title, question, kind)
                task, seed_used, error = None, None, None
                for seed in seeds:
                    try:
                        task = logic_tasks.build_facts_task(
                            facts, topics, steps, seed, question=question,
                            max_attempts=attempts,
                        )
                    except (logic_tasks.BudgetError, ValueError) as exc:
                        error = exc
                        continue
                    seed_used = seed
                    break
                if task is None:
                    cases.append(("%s: генератор не построил условие (%s)"
                                  % (tag, error), False))
                    continue
                answer = task.answer_for(question)
                scheme = _hybrid_scheme(intervals, moduli, task.scheme)
                plan_ok = False
                matters = False
                lo, hi = None, None
                if scheme is not None:
                    got = logic_tasks._hyb_plan(scheme, intervals, moduli,
                                                limit)
                    plan_ok = got[0] == answer
                    lo, hi = got[1] if got[1] else (None, None)
                    matters = logic_tasks._hybrid_matters(
                        scheme, intervals, moduli, limit)[0]
                used = logic_core.leaves(task.final)
                nodes = [node for _p, node in logic_core.subterms(task.final)]
                ivs_in = [name for name in order if ("in", name) in used]
                divs_in = [m for m in moduli
                           if ("div", ("var", "x"), ("c", m)) in nodes]
                a_in = ("in", "A") in used or ("var", "A") in used
                verified = logic_tasks._verify_hybrid(
                    task.final, intervals, question, answer, lo, hi)
                direct = logic_tasks.build_facts_task(
                    facts, topics, steps, seed_used, question=question)
                try:
                    got_api = logic_api.task_logic(
                        _hybrid_proto(facts, len(order), question, seed_used))
                    api_answer = got_api.get("answer")
                except Exception as exc:            # ошибка API -- падение
                    api_answer = "%s: %s" % (type(exc).__name__, exc)
                passed = (plan_ok and matters and verified and a_in
                          and len(ivs_in) == len(order)
                          and len(divs_in) == len(moduli)
                          and api_answer == answer == direct.answer)
                cases.append((
                    "%s: seed=%s, схема %s, ответ %s, task_logic %s, "
                    "отрезков %d/%d, делителей %d/%d, A %s, оракул %s, "
                    "matters %s, verify %s"
                    % (tag, seed_used, task.scheme, answer, api_answer,
                       len(ivs_in), len(order), len(divs_in), len(moduli),
                       a_in, plan_ok, matters, verified),
                    passed))
    return cases


def print_table(rows):
    """Таблица «конфигурация | схема | oracle_solve | схема | verify | статус»."""
    print("\n=== доступность вопросов: oracle_solve, схема, oracle_generator ===")
    print("%-20s %-20s %-16s %-16s %-16s %s"
          % ("конфигурация", "схема", "oracle_solve", "схема", "verify",
             "статус"))
    for title, scheme, solve_q, got, verify_q, ok in rows:
        print("%-20s %-20s %-16s %-16s %-16s %s"
              % (title, scheme, solve_q, got, verify_q,
                 "ok" if ok else "FAIL"))


def print_split(rows):
    """Таблица «где solve даёт длину, а verify вопрос не примет»."""
    print("\n=== solve даёт длину, verify вопрос не примет ===")
    print("%-20s %-20s %-16s %s"
          % ("конфигурация", "схема", "вопрос", "длина solve"))
    for title, scheme, question, answer in rows:
        print("%-20s %-20s %-16s %s"
              % (title, scheme, question, answer))


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
    """Запускает все блоки самопроверки facts-схем."""
    started = time.time()
    print("logic_facts_selfcheck: схем %d, конфигураций %d, темы %s, steps %d"
          % (len(logic_tasks._SCHEMES), len(CONFIGS), ",".join(TOPICS), STEPS))
    failures = 0
    failures += run(oracle_cases(),
                    "oracle_solve: min/max длины против solve")
    failures += run(generator_cases(),
                    "генератор: ответ выбранной схемы против oracle_generator")
    failures += run(equivalence_cases(),
                    "эквивалентность: counterexample(final, core)")
    failures += run(legacy_cases(), "регрессия legacy: _facts_rule_specs")
    availability, rows = availability_cases()
    failures += run(availability, "доступность вопросов по оракулам")
    print_table(rows)
    split, split_rows = split_cases()
    failures += run(split, "разделение оракулов: solve против verify")
    print_split(split_rows)
    failures += run(determinism_cases(), "детерминизм по seed")
    failures += run(budget_cases(), "бюджет: BudgetError вместо RuntimeError")
    failures += run(flat_setexpr_cases(),
                    "плоские _SetExpr и _pair_schemes: поведение прежнее")
    failures += run(multi_pool_cases(),
                    "пул 3..6 фактов: в каждой схеме все факты")
    failures += run(multi_build_cases(),
                    "3..6 фактов: final, verify, _matters")
    failures += run(multi_api_cases(), "task_logic на intervals=3..6")
    failures += run(multi_input_cases(),
                    "границы входа: имена P..U и intervals 1..6")
    failures += run(hybrid_lcm_cases(),
                    "гибриды: НОК(6, 4) = 12 и ответ 36")
    failures += run(hybrid_cases(),
                    "гибриды: отрезки + ДЕЛ, final/verify/_matters/task_logic")
    print("\nИтого провалов: %d, время: %.3f с"
          % (failures, time.time() - started))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())

