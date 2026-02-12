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
    
    print(f"科目顺序: {subject_order}")
    
    # 第一轮：用subject_order[0]科目淘汰，保留排名前4的学生
    subject = subject_order[0]
    students = sorted(students, key=lambda x: rankings[subject][x])[:4]
    print(f"第一轮后存活学生: {students}")
    
    # 第二轮：用subject_order[1]科目淘汰，保留排名前2的学生
    subject = subject_order[1]
    students = sorted(students, key=lambda x: rankings[subject][x])[:2]
    print(f"第二轮后存活学生: {students}")
    
    # 第三轮：用subject_order[2]科目淘汰，保留排名第一的学生
    subject = subject_order[2]
    students = sorted(students, key=lambda x: rankings[subject][x])[:1]
    print(f"最终冠军: {students[0]}")
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

# 构造最终矩阵
def construct_final_matrix():
    """
    构造一个最终的排名矩阵，让A-D成为潜在冠军
    :return: 3x8的排名矩阵
    """
    # 科目X：A-F排名1-6，G-H排名7-8
    subject_X = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目Y：A和D排名前2，B和C排名3-4，E和F排名5-6
    subject_Y = [1, 3, 4, 2, 5, 6, 7, 8]
    
    # 科目Z：B和C排名前2，A和D排名3-4，E和F排名5-6
    subject_Z = [3, 1, 2, 4, 5, 6, 7, 8]
    
    return [subject_X, subject_Y, subject_Z]

# 主函数
if __name__ == "__main__":
    # 测试最终矩阵
    print("测试最终矩阵：")
    final_matrix = construct_final_matrix()
    count, champions, order_champions = count_potential_champions(final_matrix)
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    
    # 输出每个科目顺序对应的冠军
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = order_champions[subject_order]
        print(f"科目顺序 {subject_order} 对应的冠军是学生 {champion}")