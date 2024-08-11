import random

def task_35627():
    '''Генерация аналогичных задач № 35627 с портала https://kuzovkin.info/one_exercise_1/35627
    Предприниматель обратился в банк с просьбой о предоставлении ссуды в размере 1000000 рублей сроком на 1 год.
    Банк выделил ему эту ссуду с годовой процентной ставкой 20% при условии погашения ссуды одним платежом в конце
    срока. Какую сумму должен через год возвратить предприниматель банку? Какие процентные деньги получит банк?
    '''
    path_to_json = 'context.json'
    data = load_constants_from_json(path_to_json)
    context = generate_random_context(data)
    while True:
      loan_amount = random.randint(100_000, 10_000_000)
      interest_rate = random.uniform(1, 30)
      duration = random.randint(2, 8)
      interest_rate = int(interest_rate*100)/100
      total_payment = loan_amount * (1 + interest_rate / 100) ** (duration)
      if abs(int(total_payment*100)-total_payment*100)<0.0000001:
        break

    question_template = (
        f"{context['scripts']} обратился в банк с просьбой о предоставлении ссуды в размере {{}} рублей сроком на {{}} {{}}. "
        f"Банк выделил ему эту ссуду с годовой процентной ставкой {{:.2f}}% при условии погашения ссуды одним платежом в "
        f"конце срока. Какую сумму должен через {{}} {{}} возвратить {context['scripts']} банку? Какие процентные деньги получит банк?")

    year_word = 'год' if duration == 1 else 'года' if duration in (2, 3, 4) else 'лет'
    question = question_template.format(loan_amount, duration, year_word, interest_rate, duration, year_word)
    task = question
    interest_money = total_payment - loan_amount

    answer = (
        f"{round(total_payment,2)}, "
        f"{round(interest_money,2) }."
    )

    return {"condition": task, "answer": answer}
result = task_35627()

def task_35628():
    '''Генерация аналогичных задач № 35628 с портала https://kuzovkin.info/one_exercise_1/35628
    Клиент взял в банке кредит 18 000 рублей на год под 14%. Он должен погашать кредит, внося
    в банк ежемесячно одинаковую сумму денег, с тем чтобы через год выплатить всю сумму, взятую
    в кредит, вместе о процентами. Сколько рублей он должен вносить в банк ежемесячно?
    '''
    path_to_json = 'context.json'
    data = load_constants_from_json(path_to_json)
    context = generate_random_context(data)
    while True:
        loan_amount = random.randint(10_000, 1_000_000)
        interest_rate = random.uniform(1, 30)
        duration = random.randint(1, 5)
        monthly_rate = interest_rate / 100 / 12
        total_months = duration * 12
        monthly_payment = loan_amount * (monthly_rate * (1 + monthly_rate) ** total_months) / ((1 + monthly_rate) ** total_months - 1)
        if abs(int(monthly_payment * 100) - monthly_payment * 100) < 0.0000001:
            break

    question_template = (
        f"{context['scripts']} взял в банке кредит {loan_amount} рублей на {duration} "
        f"{'год' if duration == 1 else ('года' if duration in (2, 3, 4) else 'лет')} под {interest_rate:.2f}%. "
        f"Он должен погашать кредит, внося в банк ежемесячно одинаковую сумму денег, с тем чтобы через заданный срок выплатить всю сумму, "
        f"взятую в кредит, вместе с процентами. Сколько рублей он должен вносить в банк ежемесячно?"
    )

    answer = f'{monthly_payment:.2f}'

    return {"condition": question_template, "answer": answer}

result = task_35628()