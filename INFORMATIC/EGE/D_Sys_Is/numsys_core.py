"""Ядро генераторов ЕГЭ № 14 «Системы счисления».

Модуль не зависит от остального кода проекта (только стандартная библиотека).
Движки (`numsys_engines.py`), спеки (`numsys_specs.py`) и обёртки
`task_<ID>()` (`numsys_tasks.py`) строятся поверх этих функций.

Соглашения:

* запись числа -- список цифр, **младшая цифра первая** (little-endian):
  так нумеруются разряды в формулировках «справа налево, начиная с нуля»;
  там, где важен порядок символов, используется `digits_msd`;
* все значения -- неотрицательные `int`: в оригинальных задачах значение
  выражения всегда положительно, поэтому отрицательное значение -- ошибка
  спеки, а не повод взять модуль;
* основание -- `int` не меньше 2 (в задачах ЕГЭ встречаются 3, 5, 7, 9, 11,
  12, 15, 16, 25, 27, 31, 36, 49, 64, 81, 121, 125, 243). Основания больше
  36 не печатаются символами, но разложение по основанию работает:
  ограничение `MAX_BASE` действует только на `to_base_string`.

Ошибки:

* `NumsysError` -- неверные аргументы (основание, цифра, отрицательное значение);
* `GenerationError` -- исчерпан бюджет попыток или размера значения
  (см. `PLAN_NUMSYS.md`, § 4.5 «Бюджет вычислений»).
"""

from collections import Counter


#: Максимальное основание, для которого цифра изображается одним символом.
MAX_BASE = 36

#: Бюджет размера значения: 20 000 бит ≈ 6 000 десятичных цифр.
MAX_BITS = 20000

#: Бюджет попыток rejection sampling (в текущем коде проекта -- `while True`).
MAX_TRIES = 200

DIGIT_CHARS = "0123456789abcdefghijklmnopqrstuvwxyz"


class NumsysError(ValueError):
    """Неверные аргументы при работе с записью числа."""


class GenerationError(RuntimeError):
    """Не удалось сгенерировать значение в рамках бюджета попыток/размера."""


def check_base(base):
    """Проверяет корректность основания системы счисления и возвращает его."""
    if isinstance(base, bool) or not isinstance(base, int):
        raise NumsysError("основание должно быть целым числом, получено %r" % (base,))
    if base < 2:
        raise NumsysError("основание должно быть не меньше 2, получено %r" % (base,))
    return base


def check_value(value):
    """Проверяет, что значение -- целое неотрицательное число."""
    if isinstance(value, bool) or not isinstance(value, int):
        raise NumsysError("значение должно быть целым числом, получено %r" % (value,))
    if value < 0:
        raise NumsysError(
            "значение должно быть неотрицательным, получено %r "
            "(в задачах № 14 значение выражения всегда положительно)" % (value,)
        )
    return value


def check_digit(digit, base):
    """Проверяет, что цифра допустима для данного основания."""
    check_base(base)
    if isinstance(digit, bool) or not isinstance(digit, int):
        raise NumsysError("цифра должна быть целым числом, получено %r" % (digit,))
    if not 0 <= digit < base:
        raise NumsysError(
            "цифра %r недопустима для основания %d" % (digit, base)
        )
    return digit


def digits_of(value, base):
    """Цифры числа в системе с основанием `base`; младшая цифра первая."""
    check_base(base)
    check_value(value)
    if value == 0:
        return [0]
    result = []
    while value:
        value, remainder = divmod(value, base)
        result.append(remainder)
    return result


def digits_msd(value, base):
    """Цифры числа в естественном порядке: старшая цифра первая."""
    return digits_of(value, base)[::-1]


def value_of(digits, base):
    """Собирает число из списка цифр (младшая цифра первая)."""
    check_base(base)
    result = 0
    for digit in reversed(digits):
        check_digit(digit, base)
        result = result * base + digit
    return result


def length_of(value, base):
    """Количество цифр (разрядов) в записи числа."""
    return len(digits_of(value, base))


def to_base_string(value, base, upper=True):
    """Запись числа строкой в системе с основанием `base` (2..36)."""
    check_base(base)
    if base > MAX_BASE:
        raise NumsysError(
            "основание %d больше %d: цифру нельзя изобразить символом, "
            "используйте digits_of()" % (base, MAX_BASE)
        )
    check_value(value)
    if value == 0:
        return "0"
    chars = DIGIT_CHARS.upper() if upper else DIGIT_CHARS
    result = []
    while value:
        value, remainder = divmod(value, base)
        result.append(chars[remainder])
    return "".join(reversed(result))


def check_budget(value, max_bits=MAX_BITS):
    """Проверяет, что значение укладывается в бюджет размера, и возвращает его."""
    check_value(value)
    if value.bit_length() > max_bits:
        raise GenerationError(
            "значение слишком велико: %d бит при бюджете %d "
            "(уменьшите показатели в спеке)" % (value.bit_length(), max_bits)
        )
    return value


def require(condition, message):
    """Поднимает `GenerationError`, если условие не выполнено (проверки спеки)."""
    if not condition:
        raise GenerationError(message)


def count_digit(value, base, digit):
    """Сколько раз цифра `digit` встречается в записи числа."""
    check_digit(digit, base)
    return digits_of(value, base).count(digit)


def count_digits_by(value, base, predicate):
    """Сколько цифр записи удовлетворяют предикату `predicate` (движок E3)."""
    return sum(1 for digit in digits_of(value, base) if predicate(digit))


def sum_digits(value, base, exclude=None):
    """Сумма цифр записи.

    `exclude` -- цифра, которую не учитываем (задачи 4412/4413: «сумма всех
    цифр, исключая шестёрки»).
    """
    digits = digits_of(value, base)
    if exclude is None:
        return sum(digits)
    check_digit(exclude, base)
    return sum(digit for digit in digits if digit != exclude)


def digit_frequencies(value, base):
    """Словарь «цифра -> сколько раз встретилась», по убыванию частоты."""
    counter = Counter(digits_of(value, base))
    return dict(sorted(counter.items(), key=lambda item: (-item[1], item[0])))


def count_distinct_digits(value, base):
    """Сколько различных цифр в записи числа (движок E4)."""
    return len(set(digits_of(value, base)))


def min_digit(value, base):
    """Минимальная цифра записи."""
    return min(digits_of(value, base))


def max_digit(value, base):
    """Максимальная цифра записи (4886/4887: «максимальная цифра»)."""
    return max(digits_of(value, base))


def first_digit(value, base):
    """Старшая (первая при чтении) цифра записи (3561: «какая первая цифра»)."""
    return digits_msd(value, base)[0]


def last_digit(value, base):
    """Младшая (последняя) цифра записи."""
    return digits_of(value, base)[0]


def position_from_right(value, base, digit):
    """Номер разряда справа налево, начиная с нуля, или `None` (задача 4417)."""
    check_digit(digit, base)
    for position, current in enumerate(digits_of(value, base)):
        if current == digit:
            return position
    return None


def is_prime(number):
    """Простое ли число (для значений цифр и небольших чисел, движок E3)."""
    if number < 2:
        return False
    if number % 2 == 0:
        return number == 2
    divisor = 3
    while divisor * divisor <= number:
        if number % divisor == 0:
            return False
        divisor += 2
    return True


def matches(digit, spec):
    """Соответствует ли цифра описанию: цифра (`int`) или диапазон `(lo, hi)`."""
    if isinstance(spec, tuple):
        low, high = spec
        return low <= digit <= high
    return digit == spec


def count_pairs(value, base, first, second):
    """Сколько раз в записи за цифрой `first` идёт подходящая `second`.

    Задачи 5136-5140: «комбинации цифр 6#», где # -- цифра из диапазона,
    и «комбинации 66». Просмотр слева направо, перекрывающиеся позиции
    считаются независимо.
    """
    digits = digits_msd(value, base)
    return sum(
        1
        for index in range(len(digits) - 1)
        if digits[index] == first and matches(digits[index + 1], second)
    )


def truncate_low(digits, count):
    """Отбрасывает `count` младших цифр (задачи 4414-4416: «удалили 3 цифры»)."""
    if count < 0:
        raise NumsysError("число отбрасываемых цифр не может быть отрицательным")
    result = list(digits[count:])
    return result or [0]


def truncate_high(digits, count):
    """Оставляет `count` младших цифр (отбрасывает старшие)."""
    if count < 0:
        raise NumsysError("число оставляемых цифр не может быть отрицательным")
    result = list(digits[:count])
    return result or [0]


def replace_digit(digits, old, new):
    """Заменяет все цифры `old` на `new` (4414-4416: «все цифры 7 заменили на 0»)."""
    return [new if digit == old else digit for digit in digits]


def zeros_to_max(digits):
    """Заменяет все нули на максимальную цифру записи (4888/4889)."""
    if not digits:
        return list(digits)
    maximum = max(digits)
    return [maximum if digit == 0 else digit for digit in digits]


def attempts(max_tries=MAX_TRIES, what="значение"):
    """Счётчик попыток для rejection sampling.

    Использование::

        for _ in attempts(what="параметры 2186"):
            value = build_value(params)
            if value > 0:
                break

    Если за `max_tries` попыток условие так и не выполнено, поднимается
    `GenerationError` -- вместо бесконечного `while True`, как в существующем
    коде проекта.
    """
    for _ in range(max_tries):
        yield
    raise GenerationError(
        "не удалось сгенерировать %s за %d попыток" % (what, max_tries)
    )
