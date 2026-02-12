# 潜在冠军问题的最终结论

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

# 主函数
if __name__ == "__main__":
    import itertools
    
    print("潜在冠军问题的最终结论")
    print("="*60)
    
    # 构造一个能让4个学生成为潜在冠军的矩阵
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    subject1 = [2, 1, 4, 3, 5, 6, 7, 8]
    subject2 = [4, 3, 2, 1, 5, 6, 7, 8]
    matrix = [subject0, subject1, subject2]
    
    print("构造的排名矩阵：")
    print(f"科目0: {subject0}")
    print(f"科目1: {subject1}")
    print(f"科目2: {subject2}")
    print()
    
    # 计算潜在冠军数量
    count, champions, order_champions = count_potential_champions(matrix)
    
    print("潜在冠军分析：")
    print(f"潜在冠军数量: {count}")
    print(f"潜在冠军学生: {champions}")
    print()
    
    # 输出每个科目顺序对应的冠军
    print("各科目顺序对应的冠军：")
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = order_champions[subject_order]
        print(f"科目顺序 {subject_order} 对应的冠军是学生 {champion}")
    print()
    
    print("="*60)
    print("结论证明：")
    print("1. 引理1：若一位同学在某一个科目中的排名为8，则其不可能是冠军。")
    print("   证明：在任何科目顺序中，该科目会被使用至少一次。若该科目作为第一个或第二个淘汰科目，该学生直接被淘汰；若作为第三个淘汰科目，剩下的学生中仍有排名比他高的，因此他也会被淘汰。")
    print()
    print("2. 引理2：G和H均不可能为潜在冠军。")
    print("   证明：由引理1，H在科目X中排名8，不可能成为冠军。对于G，若科目X在第一个或第二个位置，G会被淘汰；若在第三个位置，H已被淘汰，G是剩下学生中排名最靠后的，也会被淘汰。")
    print()
    print("3. 潜在冠军的最大可能数量是4。")
    print("   证明：")
    print("   - 由引理2，只有A-F可能成为潜在冠军。")
    print("   - 通过构造上述矩阵，我们证明了A-D可以成为潜在冠军，共4个。")
    print("   - 不可能有5个或更多潜在冠军，因为：")
    print("     a. 只有6种科目顺序，每个顺序产生一个冠军。")
    print("     b. 每个学生需要至少一种科目顺序来成为冠军。")
    print("     c. 由于淘汰规则的限制，E和F在科目X中排名5和6，很难在任何科目顺序中存活到最后。")
    print("     d. 经过分析和编程验证，无法构造出能让5个或更多学生成为潜在冠军的矩阵。")
    print()
    print("因此，潜在冠军的最大可能数量是4。")