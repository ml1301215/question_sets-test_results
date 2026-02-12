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
    
    # 第一轮：用subject_order[0]科目淘汰，保留排名前4的学生
    subject = subject_order[0]
    students = sorted(students, key=lambda x: rankings[subject][x])[:4]
    
    # 第二轮：用subject_order[1]科目淘汰，保留排名前2的学生
    subject = subject_order[1]
    students = sorted(students, key=lambda x: rankings[subject][x])[:2]
    
    # 第三轮：用subject_order[2]科目淘汰，保留排名第一的学生
    subject = subject_order[2]
    students = sorted(students, key=lambda x: rankings[subject][x])[:1]
    
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

# 构造一个成功的矩阵，让A-D成为潜在冠军
def construct_successful_matrix():
    """
    构造一个成功的排名矩阵，让A-D成为潜在冠军
    :return: 3x8的排名矩阵
    """
    # 科目0：A-F排名1-6，G-H排名7-8
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：A和C排名前2，B和D排名3-4，E和F排名5-6
    subject1 = [1, 3, 2, 4, 5, 6, 7, 8]
    
    # 科目2：B和D排名前2，A和C排名3-4，E和F排名5-6
    subject2 = [3, 1, 4, 2, 5, 6, 7, 8]
    
    return [subject0, subject1, subject2]

# 主函数
if __name__ == "__main__":
    # 测试成功的矩阵
    print("测试成功的矩阵：")
    matrix = construct_successful_matrix()
    count, champions, order_champions = count_potential_champions(matrix)
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    
    # 输出每个科目顺序对应的冠军
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = order_champions[subject_order]
        print(f"科目顺序 {subject_order} 对应的冠军是学生 {champion}")
    
    # 分析结果
    print(f"\n分析：")
    print(f"- 学生0(A)成为冠军的科目顺序：{[k for k, v in order_champions.items() if v == 0]}")
    print(f"- 学生1(B)成为冠军的科目顺序：{[k for k, v in order_champions.items() if v == 1]}")
    print(f"- 学生2(C)成为冠军的科目顺序：{[k for k, v in order_champions.items() if v == 2]}")
    print(f"- 学生3(D)成为冠军的科目顺序：{[k for k, v in order_champions.items() if v == 3]}")
    print(f"- 学生4(E)成为冠军的科目顺序：{[k for k, v in order_champions.items() if v == 4]}")
    print(f"- 学生5(F)成为冠军的科目顺序：{[k for k, v in order_champions.items() if v == 5]}")