import random


def task_27953():
    """Генерация аналогичной задачи с портала https://ege.sdamgia.ru/test?theme=71"""

    template = r"$\alpha = k \cdot 10 ^{-6} C^{-1} $"
    data = [
        {"железный рельс": 11.3},
        {"железная дверь": 11.3},
        {"алюминиевая труба": 22.2},
        {"алюминиевый потолочный карниз": 22.2},
        {"бетонный блок": 14.5},
        {"бетонная стена": 14.5},
        {"серебряный слиток": 19.5},
        {"витринное стекло": 5.9},
        {"медная проволока": 16.6},
        {"платиновая подвеска": 9}
    ]
    pair = random.choice(data)
    while True:
        material = list(pair.keys())[0]
        coefficient = template.replace("k", str(list(pair.values())[0]))
        l0 = round(random.uniform(1, 10), 1)
        delta_l = round(random.uniform(1, 50), 1) * (10 ** -3)
        alpha = list(pair.values())[0] * (10 ** -6)
        answer = delta_l / (l0 * alpha)
        if len(str(answer % 1)) < 4:
            if answer % 1 == 0:
                answer = int(answer)
                break
    task = (fr"При температуре $0$ $C^\circ$ {material} имеет длину {round(l0, 1)} м. "
            "При возрастании температуры происходит тепловое расширение материала, "
            r"и его длина, выраженная в метрах, меняется по закону $l=l_0 \cdot(1+\alpha \cdot t) $,"
            fr" где {coefficient} — коэффициент теплового расширения, $t$ — температура "
            f"(в градусах Цельсия). При какой температуре {material} удлинится "
            f"на {round(delta_l * 1000, 1)} мм? Ответ выразите в градусах Цельсия.")
    return {
        "condition": task,
        "answer": answer
    }


def task_1():
    """Задача на зависимость электрического сопротивления от температуры"""
    template = r"$\alpha = k \cdot 10 ^{-3} C^{-1}$"
    template_1 = r"$R_{20} = k1 \cdot 10 ^{-8}$"
    data = [{"медный провод": [4.3, 1.68]},
            {"железная труба": [6, 9.71]},
            {"золотой слиток": [4, 2.44]},
            {"оловянный поднос": [4.4, 11.5]},
            {"платиновая подвеска": [3.9, 10.6]}]
    pair = random.choice(data)
    while True:
        rt = round(random.uniform(1, 20), 3) * (10 ** -8)
        r20 = list(pair.values())[0][1] * (10 ** -8)
        a = list(pair.values())[0][0] * (10 ** -3)
        answer = (rt - r20) / (r20 * a) + 20
        if len(str(answer)) < 50:
            answer = round(float(answer), 2)
            if len(str(answer)) < 7:
                break
    task = (r"Зависимость сопротивления $R_t$ проводника от температуры t описывается формулой: "
            r"$$R(t) = R_{20} \times (1 + \alpha \times (t - 20))$$, где t - температура в "
            r"градусах цельсия, $R_{20} $ – сопротивление проводника при 20°С, $\alpha$ - "
            "температурный коэффициент сопротивления. При какой температуре "
            rf"{list(pair.keys())[0]} будет иметь сопротивление, равное "
            rf"${rt * (10 ** 8)}\cdot 10 ^{{-8}}$ ом-м, "
            f"если {template_1.replace('k1', str(list(pair.values())[0][1]))} ом-м, "
            f"{template.replace('k', str(list(pair.values())[0][0]))}. "
            "Ответ округлите до двух знаков после запятой.")
    return {
        "condition": task,
        "answer": answer
    }
