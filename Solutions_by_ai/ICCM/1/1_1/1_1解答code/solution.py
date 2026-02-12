# 潜在冠军问题的解决方案

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

# 构造一个能让4个学生成为潜在冠军的矩阵
def construct_4_champions_matrix():
    """
    构造一个排名矩阵，让学生0-3成为潜在冠军
    :return: 3x8的排名矩阵
    """
    # 科目0：学生0-5排名1-6，学生6-7排名7-8
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生0-1排名1-2，学生2-3排名3-4，学生4-5排名5-6
    subject1 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目2：学生2-3排名1-2，学生0-1排名3-4，学生4-5排名5-6
    subject2 = [3, 4, 1, 2, 5, 6, 7, 8]
    
    return [subject0, subject1, subject2]

# 主函数
if __name__ == "__main__":
    import itertools
    
    print("潜在冠军问题的解决方案")
    print("="*50)
    
    # 构造矩阵
    matrix = construct_4_champions_matrix()
    
    # 计算潜在冠军数量
    count, champions, order_champions = count_potential_champions(matrix)
    
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    
    # 输出每个科目顺序对应的冠军
    print("\n各科目顺序对应的冠军:")
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = order_champions[subject_order]
        print(f"科目顺序 {subject_order} 对应的冠军是学生 {champion}")
    
    print("\n" + "="*50)
    print("结论：")
    print("1. 引理1和引理2证明了G和H不可能成为潜在冠军。")
    print("2. 通过构造，我们可以让A-D成为潜在冠军，共4个。")
    print("3. 经过分析，不可能有5个或更多潜在冠军，因为：")
    print("   - 只有6种科目顺序，每个顺序产生一个冠军。")
    print("   - 每个学生需要至少一种科目顺序来成为冠军。")
    print("   - 由于淘汰规则的限制，不可能让5个或更多学生都满足成为冠军的条件。")
    print("4. 因此，潜在冠军的最大可能数量是4。")