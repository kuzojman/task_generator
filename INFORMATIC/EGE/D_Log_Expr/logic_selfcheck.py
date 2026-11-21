"""Самопроверка логических генераторов (ЕГЭ: логика, числовая прямая, биты).

В проекте нет тестовой инфраструктуры (pytest не используется), поэтому
проверки живут в одном запускаемом модуле.

Что проверяется:
  * блок `logic_rules`: каждое правило реестра прогоняется через `probe_rule`;
    если там правило не нашло цели (выборки `probe_rule` не строят константы
    1/0 и форму (a ∧ b) ∨ (¬a ∧ ¬b)), оно добирается расширенными выборками
    (`probe_extra`). Падение -- контрпример или исключение внутри правила;
  * блок `logic_api`: каждый из 9 видов собирается через обёртку, ответ имеет
    формат `{"condition": str, "answer": int}`, без префикса «Задача N.»,
    значение ответа в допустимом диапазоне, условие соответствует виду;
  * таблица с временем генерации (мс/вызов) и примером условия.

Запуск из корня проекта::

    python -m INFORMATIC.EGE.D_Log_Expr.logic_selfcheck

Запуск из этого каталога::

    python logic_selfcheck.py

Код возврата: 0 -- все проверки прошли, 1 -- есть падения.
"""
import contextlib
import io
import os
import random
import sys
import time

try:
    from . import logic_api, logic_core, logic_rules, logic_tasks
except ImportError:  # прямой запуск файлом, без пакетного импорта
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    import logic_api
    import logic_core
    import logic_rules
    import logic_tasks


#: Сколько формул прогоняет `probe_rule` на каждое правило.
PROBES = 120
#: Сколько задач генерируется на каждый вид.
RUNS = 5
#: Верхняя граница ответа в задачах на прямой (rand_intervals берёт точки 1..60).
MAX_LINE_ANSWER = 60

#: Валидные prototype для task_line_*: все четыре обязательных ключа.
LINE_PROTOTYPES = {
    "cover": "topics=morgan,implication,constants;steps=3;intervals=3;seed={seed}",
    "avoid": "topics=morgan,implication,constants;steps=3;intervals=3;seed={seed}",
    "both_min": "topics=morgan,constants;steps=2;intervals=2;seed={seed}",
    "both_max": "topics=morgan,constants;steps=2;intervals=2;seed={seed}",
    "differ_min": "topics=morgan,distributivity,constants;steps=3;intervals=2;seed={seed}",
    "differ_max": "topics=morgan,distributivity,constants;steps=3;intervals=2;seed={seed}",
}


def _probe_population(fn, make, ctx, n):
    """Прогон правила по одной выборке; счётчики как у `probe_rule`."""
    tried = ok = bad = err = 0
    for _ in range(n):
        for _, node in logic_core.subterms(make()):
            try:
                res = fn(node, ctx)
            except Exception:
                err += 1
                continue
            if res is None:
                continue
            tried += 1
            if logic_core.counterexample(node, res[0]) is None:
                ok += 1
            else:
                bad += 1
    return tried, ok, bad, err


def probe_extra(fn, n=PROBES, seed=11):
    """Выборки, которых нет в `probe_rule`: константы 1/0 и форма (a ∧ b) ∨ (¬a ∧ ¬b).

    Нужны правилам про a ∨ 0, a ∧ 1 и обратному развороту эквивалентности:
    случайные формулы `probe_rule` таких узлов не строят, и правило «молчит».
    """
    rnd = random.Random(seed)
    line_ctx = logic_rules.Ctx(rnd, lambda: logic_rules.line_lit(rnd, ("P", "Q", "R")))
    bit_ctx = logic_rules.Ctx(rnd, lambda: logic_rules.bit_lit(rnd),
                             lambda: logic_rules.bit_leaf(rnd))

    def const_line():
        return logic_rules.rand_h(
            lambda: rnd.choice((logic_core.T, logic_core.F, line_ctx.lit())), rnd, 2)

    def const_bit():
        return logic_rules.rand_h(
            lambda: rnd.choice((logic_core.T, logic_core.F, bit_ctx.lit())), rnd, 2)

    def eqv_shape():
        a, b = line_ctx.lit(), line_ctx.lit()
        return ("or", ("and", a, b),
                ("and", logic_core.negate(a), logic_core.negate(b)))

    tried = ok = bad = err = 0
    for make, ctx in ((const_line, line_ctx), (const_bit, bit_ctx),
                      (eqv_shape, line_ctx)):
        part = _probe_population(fn, make, ctx, n)
        tried, ok, bad, err = (tried + part[0], ok + part[1],
                               bad + part[2], err + part[3])
    return tried, ok, bad, err


def rule_cases(probes=PROBES):
    """Все правила реестра: применимо, верно, контрпримеры, исключения."""
    cases = []
    for topic in sorted(logic_rules.TOPICS):
        for fn in logic_rules.TOPICS[topic]:
            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                tried, ok, bad, err = logic_rules.probe_rule(fn, n=probes, seed=7)
            source = "probe_rule"
            if tried == 0:
                extra = probe_extra(fn, n=probes)
                tried, ok, bad, err = (tried + extra[0], ok + extra[1],
                                       bad + extra[2], err + extra[3])
                source = "probe_rule + расширенные выборки"
            passed = tried > 0 and bad == 0 and err == 0
            note = "%s: применимо %d, верно %d, НЕВЕРНО %d, ошибок %d" % (
                source, tried, ok, bad, err)
            if not passed:
                note += " :: " + " ".join(buffer.getvalue().split())
            cases.append(("[%s] %s -- %s" % (topic, fn.__name__, note), passed))
    return cases


def check_task(kind, data):
    """Список проблем в ответе обёртки (пустой список -- ответ в порядке)."""
    if not isinstance(data, dict):
        return ["вернулось не dict: %r" % (type(data),)]
    problems = []
    if set(data) != {"condition", "answer"}:
        problems.append("ключи %s вместо condition/answer" % sorted(data))
    text, answer = data.get("condition"), data.get("answer")
    if not isinstance(text, str) or not text.strip():
        problems.append("condition не непустая строка: %r" % (text,))
        text = ""
    if text.lstrip().startswith("Задача"):
        problems.append("в условии префикс «Задача N.»")
    if "**" in text:
        problems.append("в условии остался **")
    if isinstance(answer, bool) or not isinstance(answer, int):
        problems.append("answer не int: %r" % (answer,))
    elif kind.startswith("bit"):
        if not 1 <= answer <= logic_core.MASK:
            problems.append("A=%s вне 1..%d" % (answer, logic_core.MASK))
    elif not 1 <= answer <= MAX_LINE_ANSWER:
        problems.append("длина %s вне 1..%d" % (answer, MAX_LINE_ANSWER))
    if kind.startswith("bit"):
        if "число A" not in text:
            problems.append("в условии нет «число A»")
    elif kind.startswith("differ"):
        if "различные значения" not in text:
            problems.append("в условии нет «различные значения»")
    elif "тождественно истинна" not in text:
        problems.append("в условии нет «тождественно истинна»")
    return problems


def task_cases(runs=RUNS):
    """Каждый вид через `logic_api`: `runs` генераций, формат, время, примеры.

    -> (список проверок, список строк таблицы).
    """
    cases = []
    table = []
    missing = sorted(set(logic_tasks.KINDS) - set(logic_api.WRAPPERS))
    cases.append(("у каждого вида KINDS есть обёртка (видов: %d, обёрток: %d)"
                  % (len(logic_tasks.KINDS), len(logic_api.WRAPPERS)), not missing))
    infix, tex_infix = set(logic_core.INFIX), set(logic_core.TEX_INFIX)
    cases.append(("у каждой бинарной операции есть LaTeX-запись (INFIX: %d, TEX_INFIX: %d, "
                  "не хватает: %s)" % (len(infix), len(tex_infix),
                                       ", ".join(sorted(infix - tex_infix)) or "—"),
                  infix <= tex_infix))
    for kind in sorted(logic_api.WRAPPERS):
        make = logic_api.WRAPPERS[kind]
        problems, texts, answer, sample = [], set(), None, ""
        started = time.time()
        for run in range(runs):
            try:
                if kind in LINE_PROTOTYPES:
                    data = make(LINE_PROTOTYPES[kind].format(seed=101 + run))
                else:
                    data = make()
            except Exception as error:      # RuntimeError и любое падение генератора
                problems.append("исключение %s: %s" % (type(error).__name__, error))
                break
            problems.extend(check_task(kind, data))
            texts.add(data.get("condition"))
            answer = data.get("answer")
            if not sample:
                sample = " ".join(str(data.get("condition", "")).split())
        elapsed = (time.time() - started) * 1000.0 / max(runs, 1)
        passed = not problems
        status = "ok  " if passed else "FAIL"
        detail = "" if passed else " :: " + "; ".join(problems[:3])
        cases.append(("%-10s %d прогонов, %.1f мс/вызов, answer=%s, разных условий %d%s"
                      % (kind, runs, elapsed, answer, len(texts), detail), passed))
        table.append((kind, status, elapsed, len(texts), answer, sample[:110]))
    return cases, table


def print_table(rows):
    """Таблица «вид | статус | мс/вызов | разных условий | answer | пример»."""
    print("\n=== logic_api: время и примеры ===")
    print("%-10s %-5s %10s %8s %-7s %s"
          % ("вид", "статус", "мс/вызов", "разных", "answer", "пример условия"))
    for kind, status, elapsed, unique, answer, sample in rows:
        print("%-10s %-5s %10.1f %8d %-7s %s"
              % (kind, status, elapsed, unique, answer, sample))


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
    """Запускает все блоки самопроверки."""
    started = time.time()
    rules = sum(len(fns) for fns in logic_rules.TOPICS.values())
    print("logic_selfcheck: тем %d, правил %d, видов %d, прогонов на вид %d"
          % (len(logic_rules.TOPICS), rules, len(logic_api.WRAPPERS), RUNS))
    failures = run(rule_cases(), "logic_rules: все правила (probe_rule)")
    format_cases, rows = task_cases(RUNS)
    failures += run(format_cases, "logic_api: condition/answer по 9 видам")
    print_table(rows)
    print("\nИтого провалов: %d, время: %.3f с" % (failures, time.time() - started))
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
