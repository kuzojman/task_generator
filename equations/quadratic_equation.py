import re
import random
from sympy import symbols, Eq, solve, sympify, latex, sqrt, UnevaluatedExpr, Rational, nsolve, Abs

pattern = r'([+-]?)\\frac\s*\{\s*([^{}]*?(?:\{[^{}]*\}[^{}]*)*?)\s*\}\s*\{\s*([^{}]*?(?:\{[^{}]*\}[^{}]*)*?)\s*\}'


def simplify_equation_fractions(equation_str):
    fraction_pattern = r'\\frac\s*\{\s*(-?\d+)\s*\}\s*\{\s*(-?\d+)\s*\}'

    def simplify_fraction_match(match):
        numerator = int(match.group(1))
        denominator = int(match.group(2))
        simplified = Rational(numerator, denominator)
        return f"\\frac{{{simplified.numerator}}}{{{simplified.denominator}}}"

    simplified_equation = re.sub(fraction_pattern, simplify_fraction_match, equation_str)
    return simplified_equation


def replace_denominator(match):
    sign = match.group(1)
    numerator = match.group(2).strip()
    denominator = match.group(3).strip()

    try:
        numerator_int = int(numerator)
        denominator_int = int(denominator)

        if denominator_int == 1:
            return f"{sign}{numerator_int}"
        elif numerator_int == denominator_int:
            return f"{sign}1"
        elif abs(numerator_int) > abs(denominator_int):
            whole_part = numerator_int // denominator_int
            remainder = abs(numerator_int) % abs(denominator_int)
            if remainder == 0:
                return f"{sign}{whole_part}"
            fraction_part = f"\\frac{{{remainder}}}{{{denominator_int}}}"
            return f"{sign}{whole_part} {fraction_part}"
        else:
            return f"{sign}\\frac{{{numerator_int}}}{{{denominator_int}}}"
    except ValueError:
        return f"{sign}\\frac{{{numerator}}}{{{denominator}}}"


def replace_sign(match):
    sign = match.group(1)
    numerator = match.group(2).strip()
    denominator = match.group(3).strip()

    if denominator.startswith('-'):
        denominator = denominator[1:]
        sign = '-' if sign == '+' or sign == '' else '+'

    return f"{sign}\\frac{{{numerator}}}{{{denominator}}}"


def replace_equation_sign(expression):
    if expression.startswith("+"):
      return expression[1:]
    else:
      return expression


def find_and_replace_coefficients(equation_str):
    coefficients = re.findall(r'[A-Za-z]+_\d+', equation_str)
    coefficient_values = {}

    for coeff in set(coefficients):
        random_value = random.randint(-10, 10)
        while random_value == 0:
            random_value = random.randint(-10, 10)
        coefficient_values[coeff] = random_value
        equation_str = re.sub(rf'\b{coeff}\b', str(random_value), equation_str)

    equation_str = re.sub(r'\s+', ' ', equation_str)
    equation_str = re.sub(r'-\s*-', '+', equation_str)
    equation_str = re.sub(r'(?<!\d)-\s+', '-', equation_str)
    equation_str = re.sub(r'\+\s+', '+', equation_str)
    equation_str = re.sub(r'\b1\*?x\b', 'x', equation_str)
    equation_str = re.sub(r'\b-1\*?x\b', '-x', equation_str)
    equation_str = re.sub(r'\(([^/]+)\)/1', r'\1', equation_str)

    return equation_str


def find_and_replace_coefficients_for_sqrt(equation_str):
    coefficients = re.findall(r'[A-Za-z]+_\d+', equation_str)
    coefficient_values = {}

    for coeff in set(coefficients):
        random_value = random.randint(1, 10)
        coefficient_values[coeff] = random_value
        equation_str = re.sub(rf'\b{coeff}\b', str(random_value), equation_str)

    equation_str = re.sub(r'\s+', ' ', equation_str)
    equation_str = re.sub(r'-\s*-', '+', equation_str)
    equation_str = re.sub(r'(?<!\d)-\s+', '-', equation_str)
    equation_str = re.sub(r'\+\s+', '+', equation_str)
    equation_str = re.sub(r'\b1\*?x\b', 'x', equation_str)
    equation_str = re.sub(r'\b-1\*?x\b', '-x', equation_str)
    equation_str = re.sub(r'\(([^/]+)\)/1', r'\1', equation_str)

    return equation_str


def solve_numerically(equation_str):
    x = symbols('x')
    try:
        left_side, right_side = equation_str.split('=')

        left_expr = sympify(left_side)
        right_expr = sympify(right_side)

        numerical_solution = nsolve(Eq(left_expr, right_expr), x, 0)
        rational_solution = Rational(numerical_solution).limit_denominator(100)
        return rational_solution
    except Exception as e:
        return str(e)


def solve_numerically_abs(equation_str):
    x = symbols('x')

    left_side, right_side = equation_str.split('=')
    left_expr = sympify(left_side)
    right_expr = sympify(right_side)

    equation_pos = Eq(left_expr.subs(Abs(x), x), right_expr)
    try:
        positive_root = nsolve(equation_pos, x, 1)
        positive_root_fraction = Rational(positive_root).limit_denominator(100)
    except Exception:
        positive_root_fraction = None

    equation_neg = Eq(left_expr.subs(Abs(x), -x), right_expr)
    try:
        negative_root = nsolve(equation_neg, x, -1)
        negative_root_fraction = Rational(negative_root).limit_denominator(100)
    except Exception:
        negative_root_fraction = None

    if positive_root_fraction is not None and negative_root_fraction is not None:
      return [positive_root_fraction, negative_root_fraction]
    elif positive_root_fraction is not None:
      return [positive_root_fraction]
    elif negative_root_fraction is not None:
      return [negative_root_fraction]


def solve_randomized_equation(equation_str):
    x = symbols('x')

    while True:
        try:
            if 'Abs' in equation_str or 'sqrt' in equation_str:
                randomized_equation_str = find_and_replace_coefficients_for_sqrt(equation_str)
            else:
                randomized_equation_str = find_and_replace_coefficients(equation_str)

            left_side, right_side = randomized_equation_str.split('=')

            original_left_side = UnevaluatedExpr(sympify(left_side, evaluate=False))
            original_right_side = UnevaluatedExpr(sympify(right_side, evaluate=False))

            equation = latex(Eq(original_left_side, original_right_side))
            simplified_equation = simplify_equation_fractions(equation)
            new_equation = re.sub(pattern, replace_sign, simplified_equation)
            latex_equation = re.sub(pattern, replace_denominator, new_equation)

            latex_equation = re.sub(r'-\\frac{-', r'-\\frac{', latex_equation)
            latex_equation = re.sub(r'\\frac\{-', r'-\\frac{', latex_equation)
            latex_equation = re.sub(r'-\s*-', '+', latex_equation)
            latex_equation = re.sub(r'\+\s*-', '-', latex_equation)
            latex_equation = re.sub(r'\b1\s*\*\s*', '', latex_equation)
            latex_equation = re.sub(r'(\d+)\s*\*\s*(\d+)\s*\*', r'\1 * \2 * ', latex_equation)
            latex_equation = re.sub(r'(\d+)\s*\*\s*\(([^)]+)\)', r'(\1 * \2)', latex_equation)
            latex_equation = re.sub(r'(-?)\\frac\{((?:[^{}]|\{[^{}]*\})+)\}\{1\}', r'\1\2', latex_equation)
            latex_equation = replace_equation_sign(latex_equation)

            denominator_pattern = r'\((?:[A-Za-z]+\_\d+\*x(?:\*\*2)?\s*[\+\-]\s*){1,2}[A-Za-z]+\_\d+\)'
            if re.search(denominator_pattern, randomized_equation_str):
                numerical_solution = solve_numerically(randomized_equation_str)
                return {
                    'condition': 'решите уравнение: $' + latex_equation + '$',
                    'answer': [numerical_solution],
                }

            elif 'sqrt' in equation_str:
                numerical_solution = solve_numerically(randomized_equation_str)
                return {
                    'condition': 'решите уравнение: $' + latex_equation + '$',
                    'answer': [numerical_solution],
                }
            elif 'Abs' in equation_str:
                numerical_solution = solve_numerically_abs(randomized_equation_str)
                return {
                    'condition': 'решите уравнение: $' + latex_equation + '$',
                    'answer': numerical_solution,
                }
            else:
                left_expr = sympify(left_side)
                right_expr = sympify(right_side)

                equation = Eq(left_expr, right_expr)
                solutions = solve(equation, x)

                real_solutions = [Rational(sol).limit_denominator(100) for sol in solutions if isinstance(sol, Rational)]

                if real_solutions:
                    return {
                        'condition': 'решите уравнение: $' + latex_equation + '$',
                        'answer': real_solutions,
                    }

        except (ZeroDivisionError, ValueError, TypeError):
            continue
