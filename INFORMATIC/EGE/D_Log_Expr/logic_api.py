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

`task_logic` использует переданные отрезки как имена множеств: допустимы имена
`P`, `Q`, `R`, `S`, `T`, `U` (от 1 до 6 фактов, роли границ A за именами не
закреплены), строит по ним внутренние условия (для двух фактов -- прежний
реестр схем, для трёх и более -- комбинаторные ядерные выражения), а затем
применяет question уже к полученным вариантам. Старые
`task_line_*`/`task_bits_*` продолжают работать с прежними сигнатурами и
прежним диапазоном `intervals` 2..4.

`task_divisibility` -- отдельная задача на делимость: после `$$` обязательны
`a`, `topics`, `steps`, `seed`, а модули `b`, `c`, `d`, `e`, `f` (до шести
чисел) и уточнения `scheme` (D1..D5, только для 1--2 модулей) и `question`
(max_value/min_value) необязательны. Модули задаются подряд начиная с `a` и не
повторяются; для 3..6 модулей схема строится деревом НОК/НОД.

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
        DIV_FACT_NAMES, FACT_NAMES, LINE_TOPICS, MAX_DIV_FACTS, TaskParams,
        build_facts_task, default_topics, generate_tasks,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    import os
    import sys
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from logic_tasks import (
        DIV_FACT_NAMES, FACT_NAMES, LINE_TOPICS, MAX_DIV_FACTS, TaskParams,
        build_facts_task, default_topics, generate_tasks,
    )

try:
    from .logic_div import (
        DIV_TOPICS, MAX_MODULUS, MIN_MODULUS, build_div_task,
    )
except ImportError:  # прямой запуск файлом, без пакетного импорта
    from logic_div import (
        DIV_TOPICS, MAX_MODULUS, MIN_MODULUS, build_div_task,
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
_QUESTION_KEYS = ("min_length", "max_length", "min_value", "max_value")
#: Вопросы про число A допустимы только в гибридных facts (с ДЕЛ(x, m)).
_QUESTION_DIV_ONLY = ("min_value", "max_value")
#: facts -- от одного до шести отрезков P..U; MIN_INTERVALS/MAX_INTERVALS
#: по-прежнему относятся только к старым task_line_* (2..4).
MIN_FACT_INTERVALS, MAX_FACT_INTERVALS = 1, 6


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
    """JSON-объект facts -> {имя: (lo, hi)} для отрезков и {ключ: m} для ДЕЛ.

    Ключи ``P..U`` -- отрезки ``[lo; hi]`` (lo < hi), ключи ``a..f`` и ``D1..D6``
    -- модули ``ДЕЛ(x, m)`` из 2..999. Делители допустимы только вместе хотя бы
    с одним отрезком; при их наличии границы отрезков натуральны (lo >= 1),
    модули не повторяются, а их не больше шести.
    """
    try:
        data = json.loads(raw)
    except (TypeError, ValueError):
        raise ParamError(
            "facts: ожидается JSON-объект вида "
            '{"P":[5,30],"Q":[14,23]} или {"P":[10,55],"a":6,"b":4}'
        ) from None
    if not isinstance(data, dict):
        raise ParamError("facts: ожидается JSON-объект, получено %r" % (data,))
    if not data:
        raise ParamError("facts: нужен хотя бы один отрезок")
    bad = [
        name for name in data
        if name not in FACT_NAMES and name not in DIV_FACT_NAMES
    ]
    if bad:
        raise ParamError(
            "facts: допустимы %s и делители %s; неизвестны: %s"
            % (", ".join(FACT_NAMES), ", ".join(DIV_FACT_NAMES),
               ", ".join(bad))
        )
    has_div = any(name in DIV_FACT_NAMES for name in data)
    out, moduli = {}, []
    for name, pair in data.items():
        if name in DIV_FACT_NAMES:
            if isinstance(pair, bool) or not isinstance(pair, int):
                raise ParamError(
                    "facts.%s: ожидается целое число-делитель, получено %r"
                    % (name, pair)
                )
            if not MIN_MODULUS <= pair <= MAX_MODULUS:
                raise ParamError(
                    "facts.%s: делитель должен быть от %d до %d, получено %d"
                    % (name, MIN_MODULUS, MAX_MODULUS, pair)
                )
            moduli.append(pair)
            out[name] = pair
            continue
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
        if has_div and lo < 1:
            raise ParamError(
                "facts.%s: при наличии делителей левая граница должна быть "
                "не меньше 1" % name
            )
        out[name] = (lo, hi)
    if has_div:
        if len(moduli) != len(set(moduli)):
            raise ParamError(
                "facts: делители не должны повторяться, получено %s"
                % ", ".join(str(m) for m in moduli)
            )
        if len(moduli) > MAX_DIV_FACTS:
            raise ParamError(
                "facts: делителей не больше %d, получено %d"
                % (MAX_DIV_FACTS, len(moduli))
            )
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
        if "facts" in opts and question in _QUESTION_DIV_ONLY:
            has_div = any(name in DIV_FACT_NAMES for name in opts["facts"])
            if not has_div:
                raise ParamError(
                    "question=%s допустим только при наличии делителей "
                    "(a..f или D1..D6) в facts" % question
                )
        opts["question"] = question
    return opts


#: Ключи модулей task_divisibility: до шести чисел a..f.
DIV_MODULUS_KEYS = ("a", "b", "c", "d", "e", "f")

#: Обязательные ключи prototype для task_divisibility.
_REQUIRED_DIV_KEYS = ("a", "topics", "steps", "seed")

#: Необязательные ключи prototype для task_divisibility: модули b..f и уточнения.
_OPTIONAL_DIV_KEYS = ("b", "c", "d", "e", "f", "scheme", "question")


def _parse_div_prototype(prototype):
    """Разбор prototype для task_divisibility.

    Обязательны ``a``, ``topics``, ``steps`` и ``seed``; ``b``, ``c``, ``d``,
    ``e``, ``f``, ``scheme`` и ``question`` -- необязательные уточнения. Модули
    задаются подряд начиная с ``a``: ``a`` и ``c`` без ``b`` -- ошибка. Формат
    тот же, что у task_logic: пары key=value через ';', ровно один '=' в паре.
    """
    required = _REQUIRED_DIV_KEYS
    optional = _OPTIONAL_DIV_KEYS
    keys = required + optional
    questions = ("max_value", "min_value")
    schemes = ("D1", "D2", "D3", "D4", "D5")
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
        if key not in keys:
            raise ParamError(
                "prototype: неизвестный параметр %r; допустимы: %s"
                % (key, ", ".join(keys))
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
    for key in DIV_MODULUS_KEYS:
        if key in opts:
            opts[key] = _parse_int(key, opts[key], MIN_MODULUS, MAX_MODULUS)
    present = [key for key in DIV_MODULUS_KEYS if key in opts]
    if present:
        last = DIV_MODULUS_KEYS.index(present[-1])
        for key in DIV_MODULUS_KEYS[:last]:
            if key not in opts:
                raise ParamError(
                    "prototype: модули должны задаваться подряд начиная с a, "
                    "пропущен %r" % key
                )
    if "steps" in opts:
        opts["steps"] = _parse_int("steps", opts["steps"], MIN_STEPS, MAX_STEPS)
    if "seed" in opts:
        opts["seed"] = _parse_seed(opts["seed"])
    if "scheme" in opts:
        scheme = opts["scheme"].strip()
        if scheme not in schemes:
            raise ParamError("scheme: допустимы %s, получено %r"
                             % (", ".join(schemes), scheme))
        opts["scheme"] = scheme
    if "question" in opts:
        question = opts["question"].strip()
        if question not in questions:
            raise ParamError("question: допустимы %s, получено %r"
                             % (", ".join(questions), question))
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

    Расположение фактов P..U (пересечение, вложенность в любую сторону или
    непересечение) -- допустимые исходные данные, а не ошибка входа. При
    наличии делителей ``intervals`` может совпадать либо с числом отрезков,
    либо с общим числом фактов.
    """
    n_div = sum(1 for name in facts if name in DIV_FACT_NAMES)
    if not n_div:
        if len(facts) != n_intervals:
            raise ParamError(
                "intervals=%d не совпадает с числом отрезков в facts (%d)"
                % (n_intervals, len(facts))
            )
        return
    n_segments = len(facts) - n_div
    if n_intervals not in (n_segments, len(facts)):
        raise ParamError(
            "intervals=%d не совпадает ни с числом отрезков в facts (%d), "
            "ни с общим числом фактов (%d)"
            % (n_intervals, n_segments, len(facts))
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


def _check_div_topics(topics):
    """Темы task_divisibility -- логические темы без битовых."""
    bad = [topic for topic in topics if topic not in DIV_TOPICS]
    if bad:
        raise ParamError(
            "topics: недопустимы для задач на делимость: %s" % ", ".join(bad)
        )


def task_divisibility(prototype=None):
    """Условие на делимость: ДЕЛ(x, m) и ответ на max_value/min_value.

    Возвращает ровно ``{"condition": str, "answer": int}``. Обязательны ``a``,
    ``topics``, ``steps`` и ``seed``; ``b``..``f`` -- остальные модули (подряд,
    без пропусков и повторов), ``scheme`` (D1..D5, только для 1--2 модулей) и
    ``question`` (max_value/min_value) -- необязательные уточнения. Например::

        url=INFORMATIC.EGE.D_Log_Expr.logic_api||task_divisibility$$a=6;b=4;topics=morgan,implication;steps=3;seed=1

    Модули ``a``..``f`` -- из 2..999; в двухфактных схемах ни один не делит
    другой, НОК(a, b) <= 2520, у D5 НОД > 1. Для 3..6 модулей схема строится
    деревом НОК/НОД, период НОК(moduli) не больше 10080, и каждый модуль должен
    влиять на ответ. Несовместимый вход -- ParamError, исчерпанный бюджет --
    BudgetError.
    """
    opts = _parse_div_prototype(prototype)
    required = _REQUIRED_DIV_KEYS
    missing = [key for key in required if key not in opts]
    if missing:
        raise ParamError(
            "task_divisibility: обязательны параметры %s; отсутствуют: %s"
            % (", ".join(required), ", ".join(missing))
        )
    moduli = tuple(opts[key] for key in DIV_MODULUS_KEYS if key in opts)
    if len(set(moduli)) != len(moduli):
        raise ParamError(
            "moduli: модули не должны повторяться, получено %s"
            % ", ".join(str(m) for m in moduli)
        )
    topics = opts["topics"]
    steps = opts["steps"]
    seed = opts["seed"]
    _check_div_topics(topics)
    if steps < len(topics):
        raise ParamError(
            "steps=%d меньше числа явно заданных тем (%d)"
            % (steps, len(topics))
        )
    try:
        built = build_div_task(
            moduli, topics=topics, steps=steps, seed=seed,
            scheme=opts.get("scheme"), question=opts.get("question"),
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
