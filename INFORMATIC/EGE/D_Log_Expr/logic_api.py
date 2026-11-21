"""Адаптер логического конструктора к контракту `task_api.py`.

`task_api.py` грузит модуль по строке `модуль||функция` и отдаёт результат в
JSON как есть, поэтому обёртки возвращают ровно
`{"condition": str, "answer": int}`.

Для всех `task_line_*` после `$$` обязательны ровно четыре параметра:
`topics`, `steps`, `intervals`, `seed`. Если `$$` нет, отсутствует любой ключ
или значение неверно, поднимается `ParamError` до вызова `generate_tasks`.

`topics` -- непустой список допустимых тем для одной задачи. `steps` -- точное
число преобразований от 1 до 8, не меньше числа тем; лишние шаги берутся только
из указанных тем. `intervals` -- ровно столько заданных отрезков в условии, не
считая A. `seed` -- явно заданное целое; 0 допустим.

`task_bits_*` не используют `prototype` и сохраняют прежний путь.

Рекомендуемая точка входа для новых вызовов -- `task_logic`. В её prototype
обязательны `facts`, `topics`, `steps`, `intervals`, `seed`; необязателен
`question` (`min_length` или `max_length`). Например::

    url=INFORMATIC.EGE.D_Log_Expr.logic_api||task_logic$$facts={"P":[5,30],"Q":[14,23]};topics=morgan,implication;steps=3;intervals=2;seed=1

`task_logic` использует переданные отрезки как имена множеств (P и Q не
закреплены за ролями границ A), строит по ним несколько внутренних условий
(например, I ⊆ A ⊆ U и U ⊆ A), а затем применяет question уже к полученным
вариантам. Старые `task_line_*`/`task_bits_*` продолжают работать с прежними
сигнатурами.

Условие берётся из `Task.text` -- без префикса «Задача N.», который добавляет
`Task.statement()`.

Пример вызова::

    url=INFORMATIC.EGE.D_Log_Expr.logic_api||task_line_cover$$topics=morgan,implication,constants;steps=3;intervals=3;seed=1

`unique_skeleton=False`: для вызова одной задачи этот флаг не является причиной
отбраковки, потому что `seen_sk` пуст до первой принятой задачи. Он ограничивает
только повторы среди нескольких задач одного вызова.

`task_line_*` всегда идут с `seed`: один вызов `generate_tasks` с фиксированным
бюджетом `MAX_ATTEMPTS`. Если задача не собралась, поднимается `BudgetError`;
темы, число шагов, число отрезков и seed не изменяются.
"""
import json

try:
    from task_errors import BudgetError, ParamError
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..", "..")
    ))
    from task_errors import BudgetError, ParamError

try:
    from .logic_tasks import (
        FACT_NAMES, LINE_TOPICS, TaskParams, build_facts_task, default_topics,
        generate_tasks,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from logic_tasks import (
        FACT_NAMES, LINE_TOPICS, TaskParams, build_facts_task, default_topics,
        generate_tasks,
    )


#: Лимит попыток на один вызов генератора.
MAX_ATTEMPTS = 2000

#: Максимальная длина prototype.
MAX_PROTOTYPE = 512

#: Максимум ASCII-цифр в steps/intervals до int().
MAX_INT_TEXT = 20

#: После необязательного знака seed допускается от 1 до 19 ASCII-цифр.
MAX_SEED_DIGITS = 19

#: Допустимый диапазон seed: signed 64-bit, включая 0.
MIN_SEED = -(2 ** 63)
MAX_SEED = 2 ** 63 - 1

#: Границы steps и intervals.
MIN_STEPS, MAX_STEPS = 1, 8
MIN_INTERVALS, MAX_INTERVALS = 2, 4

#: Для task_line_* все четыре ключа обязательны.
_REQUIRED_LINE_KEYS = ("topics", "steps", "intervals", "seed")
_PROTO_KEYS = _REQUIRED_LINE_KEYS

#: Для task_logic facts/steps обязательны; question -- нет.
_REQUIRED_FACTS_KEYS = ("facts", "topics", "steps", "intervals", "seed")
_OPTIONAL_FACTS_KEYS = ("question",)
_FACTS_PROTO_KEYS = _REQUIRED_FACTS_KEYS + _OPTIONAL_FACTS_KEYS
_QUESTION_KEYS = ("min_length", "max_length")
MIN_FACT_INTERVALS, MAX_FACT_INTERVALS = 1, 4


def _is_ascii_digits(text):
    """Только непустые ASCII-цифры: int() после этой проверки гарантирован."""
    return bool(text) and text.isascii() and text.isdigit()


def _parse_int(name, raw, low, high):
    """Целое без знака в диапазоне [low, high]."""
    text = raw.strip()
    if len(text) > MAX_INT_TEXT:
        raise ParamError(f"{name}: значение длиннее {MAX_INT_TEXT} символов")
    if not _is_ascii_digits(text):
        raise ParamError(f"{name}: ожидается целое число, получено {raw!r}")
    value = int(text)
    if not low <= value <= high:
        raise ParamError(f"{name}: допустимо от {low} до {high}, получено {value}")
    return value


def _parse_seed(raw):
    """Целое со знаком в signed 64-bit; 0 -- допустимый seed."""
    text = raw.strip()
    digits = text[1:] if text[:1] in ("+", "-") else text
    if not (1 <= len(digits) <= MAX_SEED_DIGITS) or not _is_ascii_digits(digits):
        raise ParamError(
            "seed: ожидается от 1 до %d ASCII-цифр после необязательного знака, "
            "получено %r" % (MAX_SEED_DIGITS, raw)
        )
    value = int(text)
    if not MIN_SEED <= value <= MAX_SEED:
        raise ParamError(
            f"seed: допустимый диапазон от {MIN_SEED} до {MAX_SEED}"
        )
    return value


def _parse_prototype(prototype):
    """'key=value;...' -> dict с уже проверенными значениями."""
    if prototype is None:
        return {}
    if not isinstance(prototype, str):
        raise ParamError("prototype должен быть строкой")
    if len(prototype) > MAX_PROTOTYPE:
        raise ParamError(f"prototype: длиннее {MAX_PROTOTYPE} символов")
    if prototype == "":
        return {}
    opts = {}
    for part in prototype.split(";"):
        if not part:
            raise ParamError("prototype: пустой фрагмент между ';'")
        if part.count("=") != 1:
            raise ParamError(f"prototype: ожидается key=value, получено {part!r}")
        key, raw = part.split("=")
        if not key:
            raise ParamError("prototype: пустой ключ")
        if key not in _PROTO_KEYS:
            raise ParamError(
                "prototype: неизвестный параметр %r; допустимы: %s"
                % (key, ", ".join(_PROTO_KEYS))
            )
        if key in opts:
            raise ParamError("prototype: параметр %r задан дважды" % key)
        if not raw.strip():
            raise ParamError("prototype: пустое значение параметра %r" % key)
        opts[key] = raw
    if "topics" in opts:
        topics = [item.strip() for item in opts["topics"].split(",")]
        if any(not item for item in topics):
            raise ParamError("topics: пустая тема в списке")
        if len(set(topics)) != len(topics):
            raise ParamError("topics: темы не должны повторяться")
        opts["topics"] = tuple(topics)
    if "steps" in opts:
        opts["steps"] = _parse_int("steps", opts["steps"], MIN_STEPS, MAX_STEPS)
    if "intervals" in opts:
        opts["intervals"] = _parse_int(
            "intervals", opts["intervals"], MIN_INTERVALS, MAX_INTERVALS
        )
    if "seed" in opts:
        opts["seed"] = _parse_seed(opts["seed"])
    return opts


def _parse_facts(raw):
    """JSON-объект facts -> {имя: (левая граница, правая граница)}."""
    try:
        data = json.loads(raw)
    except (TypeError, ValueError):
        raise ParamError(
            "facts: ожидается JSON-объект вида "
            '{"P":[5,30],"Q":[14,23]}'
        ) from None
    if not isinstance(data, dict):
        raise ParamError("facts: ожидается JSON-объект, получено %r" % (data,))
    if not data:
        raise ParamError("facts: нужен хотя бы один отрезок")
    bad = [name for name in data if name not in FACT_NAMES]
    if bad:
        raise ParamError(
            "facts: допустимы только %s; неизвестны: %s"
            % (", ".join(FACT_NAMES), ", ".join(bad))
        )
    out = {}
    for name, pair in data.items():
        if not isinstance(pair, list) or len(pair) != 2:
            raise ParamError(
                "facts.%s: ожидается [левая; правая], получено %r"
                % (name, pair)
            )
        lo, hi = pair
        if (isinstance(lo, bool) or not isinstance(lo, int)
                or isinstance(hi, bool) or not isinstance(hi, int)):
            raise ParamError(
                "facts.%s: границы должны быть целыми, получено %r"
                % (name, pair)
            )
        if lo >= hi:
            raise ParamError(
                "facts.%s: левая граница должна быть меньше правой" % name
            )
        out[name] = (lo, hi)
    return out


def _parse_facts_prototype(prototype):
    """Разбор prototype для task_logic; facts остаются заданными отрезками."""
    if prototype is None:
        return {}
    if not isinstance(prototype, str):
        raise ParamError("prototype должен быть строкой")
    if len(prototype) > MAX_PROTOTYPE:
        raise ParamError(f"prototype: длиннее {MAX_PROTOTYPE} символов")
    if prototype == "":
        return {}
    opts = {}
    for part in prototype.split(";"):
        if not part:
            raise ParamError("prototype: пустой фрагмент между ';'")
        if part.count("=") != 1:
            raise ParamError(f"prototype: ожидается key=value, получено {part!r}")
        key, raw = part.split("=")
        if not key:
            raise ParamError("prototype: пустой ключ")
        if key not in _FACTS_PROTO_KEYS:
            raise ParamError(
                "prototype: неизвестный параметр %r; допустимы: %s"
                % (key, ", ".join(_FACTS_PROTO_KEYS))
            )
        if key in opts:
            raise ParamError("prototype: параметр %r задан дважды" % key)
        if not raw.strip():
            raise ParamError("prototype: пустое значение параметра %r" % key)
        opts[key] = raw
    if "topics" in opts:
        topics = [item.strip() for item in opts["topics"].split(",")]
        if any(not item for item in topics):
            raise ParamError("topics: пустая тема в списке")
        if len(set(topics)) != len(topics):
            raise ParamError("topics: темы не должны повторяться")
        opts["topics"] = tuple(topics)
    if "steps" in opts:
        opts["steps"] = _parse_int("steps", opts["steps"], MIN_STEPS, MAX_STEPS)
    if "intervals" in opts:
        opts["intervals"] = _parse_int(
            "intervals", opts["intervals"],
            MIN_FACT_INTERVALS, MAX_FACT_INTERVALS,
        )
    if "seed" in opts:
        opts["seed"] = _parse_seed(opts["seed"])
    if "facts" in opts:
        opts["facts"] = _parse_facts(opts["facts"])
    if "question" in opts:
        question = opts["question"].strip()
        if question not in _QUESTION_KEYS:
            raise ParamError(
                "question: допустимы %s, получено %r"
                % (", ".join(_QUESTION_KEYS), question)
            )
        opts["question"] = question
    return opts


def _check_topics(kinds, topics):
    """Проверяет, что темы допустимы хотя бы для одного из видов."""
    allowed = set()
    for kind in kinds:
        allowed.update(default_topics(kind))
    bad = [topic for topic in topics if topic not in allowed]
    if bad:
        raise ParamError(
            "topics: недопустимы для видов %s: %s"
            % (", ".join(kinds), ", ".join(bad))
        )


def _as_api(task):
    return {"condition": task.text, "answer": int(task.answer)}


def _one(kinds, topics=None, steps=(2, 4), n_intervals=3, max_attempts=MAX_ATTEMPTS):
    """Одна задача выбранного вида в формате API.

    -> {"condition": str, "answer": int}. Если задача не собралась ни за
    `max_attempts`, ни за 4 * `max_attempts` попыток -- RuntimeError.
    """
    params = TaskParams(kinds=kinds, topics=topics, steps=steps,
                        n_intervals=n_intervals,
                        each_topic=False, unique_skeleton=False, tex=True)
    for attempt in (max_attempts, 4 * max_attempts):
        tasks = generate_tasks(1, params=params, max_attempts=attempt, verbose=False)
        if tasks:
            task = tasks[0]
            return {"condition": task.text, "answer": int(task.answer)}
    raise RuntimeError("не удалось собрать задачу: kinds=%s, topics=%s" % (kinds, topics))


def _line_one(kinds, prototype):
    """Одна задача task_line_* только с явно заданными четырьмя параметрами."""
    opts = _parse_prototype(prototype)
    missing = [key for key in _REQUIRED_LINE_KEYS if key not in opts]
    if missing:
        raise ParamError(
            "task_line_*: обязательны параметры %s; отсутствуют: %s"
            % (", ".join(_REQUIRED_LINE_KEYS), ", ".join(missing))
        )
    topics = opts["topics"]
    steps = opts["steps"]
    n_intervals = opts["intervals"]
    seed = opts["seed"]
    _check_topics(kinds, topics)
    if steps < len(topics):
        raise ParamError(
            "steps=%d меньше числа явно заданных тем (%d)"
            % (steps, len(topics))
        )
    params = TaskParams(kinds=kinds, topics=topics, steps=steps,
                        n_intervals=n_intervals,
                        exact_intervals=True, each_topic=True,
                        unique_skeleton=False, tex=True,
                        no_repeat_operands=True)
    tasks = generate_tasks(1, seed=seed, params=params,
                           max_attempts=MAX_ATTEMPTS, verbose=False)
    if tasks:
        return _as_api(tasks[0])
    raise BudgetError(
        "не удалось собрать задачу за %d попыток: kinds=%s, topics=%s, "
        "steps=%s, intervals=%s, seed=%r"
        % (MAX_ATTEMPTS, kinds, topics, steps, n_intervals, seed)
    )


def _check_facts_topics(topics):
    """Темы task_logic -- только темы задач на прямой."""
    bad = [topic for topic in topics if topic not in LINE_TOPICS]
    if bad:
        raise ParamError(
            "topics: недопустимы для задач на прямой: %s" % ", ".join(bad)
        )


def _check_facts(facts, n_intervals):
    """Число отрезков проверяется до генерации.

    Расположение P/Q (пересечение, вложенность в любую сторону или
    непересечение) -- допустимые исходные данные, а не ошибка входа.
    """
    if len(facts) != n_intervals:
        raise ParamError(
            "intervals=%d не совпадает с числом отрезков в facts (%d)"
            % (n_intervals, len(facts))
        )


def task_logic(prototype=None):
    """Рекомендуемая точка входа: условие из facts и ответ на question.

    Возвращает ровно ``{"condition": str, "answer": int}``. Сначала строятся
    применимые внутренние условия по facts, затем вопрос
    ``min_length``/``max_length`` фильтрует уже полученные варианты;
    среди подходящих вариант выбирается детерминированно по seed. Если
    вопрос не задан, вариант и вопрос выбираются по seed только среди
    вопросов с конечным ответом.
    """
    opts = _parse_facts_prototype(prototype)
    missing = [key for key in _REQUIRED_FACTS_KEYS if key not in opts]
    if missing:
        raise ParamError(
            "task_logic: обязательны параметры %s; отсутствуют: %s"
            % (", ".join(_REQUIRED_FACTS_KEYS), ", ".join(missing))
        )
    facts = opts["facts"]
    topics = opts["topics"]
    steps = opts["steps"]
    n_intervals = opts["intervals"]
    seed = opts["seed"]
    question = opts.get("question")
    _check_facts(facts, n_intervals)
    _check_facts_topics(topics)
    if steps < len(topics):
        raise ParamError(
            "steps=%d меньше числа явно заданных тем (%d)"
            % (steps, len(topics))
        )
    try:
        built = build_facts_task(
            facts, topics, steps, seed, question=question,
            tex=True, max_attempts=MAX_ATTEMPTS,
        )
    except ValueError as error:
        raise ParamError(str(error)) from error
    return {"condition": built.condition, "answer": int(built.answer)}


def task_line_cover(prototype=None):
    """Прямая: A ∨ H тождественно истинна; наименьшая возможная длина A."""
    return _line_one(("cover",), prototype)


def task_line_avoid(prototype=None):
    """Прямая: ¬A ∨ H тождественно истинна; наибольшая возможная длина A."""
    return _line_one(("avoid",), prototype)


def task_line_both_min(prototype=None):
    """Прямая: (¬A ∨ H1) ∧ (A ∨ H2) тождественно истинна; наименьшая длина A."""
    return _line_one(("both_min",), prototype)


def task_line_both_max(prototype=None):
    """Прямая: (¬A ∨ H1) ∧ (A ∨ H2) тождественно истинна; наибольшая длина A."""
    return _line_one(("both_max",), prototype)


def task_line_differ_min(prototype=None):
    """Прямая: два выражения различны при любом x; наименьшая длина A."""
    return _line_one(("differ_min",), prototype)


def task_line_differ_max(prototype=None):
    """Прямая: два выражения различны при любом x; наибольшая длина A."""
    return _line_one(("differ_max",), prototype)


def task_bits_min():
    """Биты: H → (x & A ≠ 0) при любом x; наименьшее A."""
    return _one(("bitmin",), topics=("bit_test", "const_split", "bit_not"))


def task_bits_max():
    """Биты: (x & A ≠ 0) → H при любом x; наибольшее A."""
    return _one(("bitmax",), topics=("bit_test", "const_split", "bit_not"))


def task_bits_max0():
    """Биты: H → (x & A = 0) при любом x; наибольшее A."""
    return _one(("bitmax0",), topics=("bit_test", "const_split", "bit_not"))


#: Вид задачи -> обёртка (нужен самопроверке и как справка по URL).
WRAPPERS = {
    "cover": task_line_cover,
    "avoid": task_line_avoid,
    "both_min": task_line_both_min,
    "both_max": task_line_both_max,
    "differ_min": task_line_differ_min,
    "differ_max": task_line_differ_max,
    "bitmin": task_bits_min,
    "bitmax": task_bits_max,
    "bitmax0": task_bits_max0,
}
