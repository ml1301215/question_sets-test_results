import itertools

# 模拟淘汰过程的函数
def simulate_elimination(rankings, subject_order):
    """
    模拟淘汰过程，返回最终冠军
    :param rankings: 3x8的矩阵，rankings[i][j]表示科目i中学生j的排名（1-8）
    :param subject_order: 科目顺序，例如[0,1,2]表示先科目0，再科目1，再科目2
    :return: 冠军学生的索引（0-7）
    """
    students = list(range(8))  # 所有学生的索引
    
    print(f"开始淘汰过程，科目顺序: {subject_order}")
    
    # 第一轮：用subject_order[0]科目淘汰，保留排名前4的学生
    subject = subject_order[0]
    print(f"第一轮使用科目{subject}，学生排名:")
    for s in students:
        print(f"  学生{s}: 排名{rankings[subject][s]}")
    students = sorted(students, key=lambda x: rankings[subject][x])[:4]
    print(f"第一轮后存活学生: {students}")
    
    # 第二轮：用subject_order[1]科目淘汰，保留排名前2的学生
    subject = subject_order[1]
    print(f"第二轮使用科目{subject}，学生排名:")
    for s in students:
        print(f"  学生{s}: 排名{rankings[subject][s]}")
    students = sorted(students, key=lambda x: rankings[subject][x])[:2]
    print(f"第二轮后存活学生: {students}")
    
    # 第三轮：用subject_order[2]科目淘汰，保留排名第一的学生
    subject = subject_order[2]
    print(f"第三轮使用科目{subject}，学生排名:")
    for s in students:
        print(f"  学生{s}: 排名{rankings[subject][s]}")
    students = sorted(students, key=lambda x: rankings[subject][x])[:1]
    print(f"最终冠军: 学生{students[0]}")
    print()
    
    return students[0]

# 计算潜在冠军数量的函数
def count_potential_champions(rankings):
    """
    计算潜在冠军的数量
    :param rankings: 3x8的矩阵，rankings[i][j]表示科目i中学生j的排名（1-8）
    :return: (潜在冠军的数量, 潜在冠军学生集合, 各科目顺序对应的冠军)
    """
    champions = set()
    order_champions = {}
    # 遍历所有6种科目顺序
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = simulate_elimination(rankings, subject_order)
        champions.add(champion)
        order_champions[subject_order] = champion
    return len(champions), champions, order_champions

# 构造最终的矩阵
def construct_final_matrix():
    """
    构造一个最终的排名矩阵，尝试让学生0-5都成为潜在冠军
    :return: 3x8的排名矩阵
    """
    # 科目0：学生0-7依次排名1-8
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生4和5排名前2，学生0和1排名3-4，学生2和3排名5-6
    subject1 = [3, 4, 5, 6, 1, 2, 7, 8]
    
    # 科目2：学生2和3排名前2，学生0和1排名3-4，学生4和5排名5-6
    subject2 = [3, 4, 1, 2, 5, 6, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个让学生4成为冠军的矩阵
def construct_for_4():
    """
    构造一个排名矩阵，让学生4在特定科目顺序中成为冠军
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生4和0排名前2，学生1和2排名3-4，学生3和5排名5-6
    subject1 = [2, 3, 4, 5, 1, 6, 7, 8]
    
    # 科目2：学生4和0排名前2，学生1和2排名3-4，学生3和5排名5-6
    subject2 = [2, 3, 4, 5, 1, 6, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个让学生5成为冠军的矩阵
def construct_for_5():
    """
    构造一个排名矩阵，让学生5在特定科目顺序中成为冠军
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生5和1排名前2，学生0和2排名3-4，学生3和4排名5-6
    subject1 = [3, 2, 4, 5, 6, 1, 7, 8]
    
    # 科目2：学生5和1排名前2，学生0和2排名3-4，学生3和4排名5-6
    subject2 = [3, 2, 4, 5, 6, 1, 7, 8]
    
    return [subject0, subject1, subject2]

# 主函数
if __name__ == "__main__":
    # 测试最终矩阵
    print("测试最终构造的矩阵：")
    final_matrix = construct_final_matrix()
    count, champions, order_champions = count_potential_champions(final_matrix)
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    print(f"各科目顺序对应的冠军: {order_champions}")
    
    # 测试让学生4成为冠军的矩阵
    print("\n\n测试让学生4成为冠军的矩阵：")
    matrix_for_4 = construct_for_4()
    count, champions, order_champions = count_potential_champions(matrix_for_4)
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    print(f"各科目顺序对应的冠军: {order_champions}")
    
    # 测试让学生5成为冠军的矩阵
    print("\n\n测试让学生5成为冠军的矩阵：")
    matrix_for_5 = construct_for_5()
    count, champions, order_champions = count_potential_champions(matrix_for_5)
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    print(f"各科目顺序对应的冠军: {order_champions}")