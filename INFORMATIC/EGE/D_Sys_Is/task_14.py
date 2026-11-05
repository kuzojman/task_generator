from random import randint
import re

def solve_ege_expression(expr_str, base, target_digit):
    """Вычисляет выражение в заданной системе счисления и считает количество цифр."""
    val = eval(expr_str)
    if val < 0:
        val = abs(val)
    
    if val == 0:
        digits = [0]
    else:
        digits = []
        temp = val
        while temp > 0:
            digits.append(temp % base)
            temp //= base
            
    return digits.count(target_digit), val


def generate_ege_task_14(sample_expression):
    """
    Генератор задач ЕГЭ №14 по произвольному образцу (шаблону).
    Ищет в образце метки {c1}, {c2}..., {base}, {p1}, {p2}, {sub} 
    и заменяет их случайными значениями.
    """
    coefficients = re.findall(r'\{c\d+\}', sample_expression)
    powers = re.findall(r'\{p\d+\}', sample_expression)
    bases = re.findall(r'\{base\}', sample_expression)
    subs = re.findall(r'\{sub\}', sample_expression)
    
    base = randint(3, 8)
    parsed_expr = sample_expression
    
    for c in coefficients:
        rand_c = randint(2, 9)
        parsed_expr = parsed_expr.replace(c, str(rand_c))
        
    for p in powers:
        rand_p = randint(500, 2500)
        parsed_expr = parsed_expr.replace(p, str(rand_p))
        
    for b in bases:
        parsed_expr = parsed_expr.replace(b, str(base))
        
    for s in subs:
        rand_sub = randint(10, 2000)
        parsed_expr = parsed_expr.replace(s, str(rand_sub))
        
    target_digit = base - 1
    count, val = solve_ege_expression(parsed_expr, base, target_digit)
    
    condition = f"Значение арифметического выражения \\({parsed_expr.replace('**', '^')}\\) записали в системе счисления с основанием \\({base}\\). Сколько цифр \\({target_digit}\\) в такой записи?"
    
    return {
        "condition": condition,
        "answer": str(count)
    }



