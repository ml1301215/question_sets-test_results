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

# 计算6个科目顺序对应的冠军
def calculate_champions(rankings):
    """
    计算6个科目顺序对应的冠军
    :param rankings: 3x8的矩阵，rankings[i][j]表示科目i中学生j的排名（1-8）
    :return: 6个科目顺序对应的冠军列表
    """
    champions = []
    # 遍历所有6种科目顺序
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = simulate_elimination(rankings, subject_order)
        champions.append(champion)
    return champions

# 找到最大冠军数量的矩阵
def find_max_champions():
    """
    穷举所有符合条件的矩阵，找到最大冠军数量
    :return: (最大冠军数量, 对应的矩阵列表, 对应的冠军列表)
    """
    # 科目X固定
    subject_X = [1, 2, 3, 4, 5, 6, 7, 8]
    
    max_champions_count = 0
    max_champions_matrices = []
    max_champions_list = []
    
    # 生成所有可能的科目Y：1-8的排列，且第8位（索引7）是8
    # 即生成前7个位置的排列，然后在第8位放8
    count_Y = 0
    total_matrices = 0
    
    for perm_Y in itertools.permutations(range(1, 8)):
        count_Y += 1
        # 构建科目Y：前7个元素是perm_Y，第8个元素是8
        subject_Y = list(perm_Y) + [8]
        
        # 生成所有可能的科目Z：1-8的排列，且第7位（索引6）或第8位（索引7）是8
        # 情况1：科目Z中H（索引7）的排名为8
        for perm_Z in itertools.permutations(range(1, 8)):
            total_matrices += 1
            # 构建科目Z：前7个元素是perm_Z，第8个元素是8
            subject_Z = list(perm_Z) + [8]
            
            # 构建排名矩阵
            rankings = [subject_X, subject_Y, subject_Z]
            
            # 计算冠军
            champions = calculate_champions(rankings)
            # 只考虑A-F（索引0-5）作为冠军
            valid_champions = [c for c in champions if c < 6]
            champions_count = len(set(valid_champions))
            
            # 更新最大冠军数量
            if champions_count > max_champions_count:
                max_champions_count = champions_count
                max_champions_matrices = [rankings]
                max_champions_list = [champions]
                print(f"找到新的最大冠军数量: {max_champions_count}")
                print(f"对应的矩阵:")
                print(f"科目X: {subject_X}")
                print(f"科目Y: {subject_Y}")
                print(f"科目Z: {subject_Z}")
                print(f"对应的冠军: {champions}")
                print(f"已处理矩阵数: {total_matrices}")
                print()
            elif champions_count == max_champions_count and max_champions_count > 0:
                max_champions_matrices.append(rankings)
                max_champions_list.append(champions)
        
        # 情况2：科目Z中G（索引6）的排名为8，H（索引7）的排名不是8
        for perm_Z in itertools.permutations(range(1, 8)):
            total_matrices += 1
            # 构建科目Z：前6个元素是perm_Z[0:6]，第7个元素是8，第8个元素是perm_Z[6]
            subject_Z = list(perm_Z[0:6]) + [8] + [perm_Z[6]]
            
            # 构建排名矩阵
            rankings = [subject_X, subject_Y, subject_Z]
            
            # 计算冠军
            champions = calculate_champions(rankings)
            # 只考虑A-F（索引0-5）作为冠军
            valid_champions = [c for c in champions if c < 6]
            champions_count = len(set(valid_champions))
            
            # 更新最大冠军数量
            if champions_count > max_champions_count:
                max_champions_count = champions_count
                max_champions_matrices = [rankings]
                max_champions_list = [champions]
                print(f"找到新的最大冠军数量: {max_champions_count}")
                print(f"对应的矩阵:")
                print(f"科目X: {subject_X}")
                print(f"科目Y: {subject_Y}")
                print(f"科目Z: {subject_Z}")
                print(f"对应的冠军: {champions}")
                print(f"已处理矩阵数: {total_matrices}")
                print()
            elif champions_count == max_champions_count and max_champions_count > 0:
                max_champions_matrices.append(rankings)
                max_champions_list.append(champions)
        
        # 每处理100个科目Y，输出进度
        if count_Y % 100 == 0:
            print(f"已处理科目Y: {count_Y}, 总矩阵数: {total_matrices}")
    
    return max_champions_count, max_champions_matrices, max_champions_list

# 主函数
if __name__ == "__main__":
    print("寻找最大冠军数量的矩阵")
    print("=" * 60)
    print("条件：")
    print("1. 科目X固定为: [1, 2, 3, 4, 5, 6, 7, 8]")
    print("2. 科目Y是1-8的排列，且H的排名为8")
    print("3. 科目Z是1-8的排列，且G或H的排名为8")
    print("4. 只考虑A-F（索引0-5）作为潜在冠军")
    print("=" * 60)
    
    max_count, matrices, champions_list = find_max_champions()
    
    print("\n" + "=" * 60)
    print("最终结果：")
    print(f"最大冠军数量: {max_count}")
    print(f"找到的矩阵数量: {len(matrices)}")
    
    if len(matrices) > 0:
        print("\n一个符合条件的矩阵：")
        print(f"科目X: {matrices[0][0]}")
        print(f"科目Y: {matrices[0][1]}")
        print(f"科目Z: {matrices[0][2]}")
        print(f"对应的冠军: {champions_list[0]}")
        
        # 分析每个学生成为冠军的次数
        champion_counts = {i: 0 for i in range(6)}
        for champion in champions_list[0]:
            if champion < 6:
                champion_counts[champion] += 1
        
        print("\n每个学生成为冠军的次数：")
        for student in range(6):
            print(f"学生{student}: {champion_counts[student]}次")
    
    print("\n结论：")
    print(f"潜在冠军的最大可能数量是{max_count}")