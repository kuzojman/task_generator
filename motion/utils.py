def generate_context(file_json, category):
  '''Функция возвращает список из файла-json. Функция изиз файла-json возвращает список возможных вариантов сюжета для задачи,
  необходимо передать файл-json и требуемую категорию. Возвращает список'''
  with open(file_json, 'r', encoding='utf8') as my_file:
    templates = my_file.read()
    context = json.loads(templates)
  return context[category]
