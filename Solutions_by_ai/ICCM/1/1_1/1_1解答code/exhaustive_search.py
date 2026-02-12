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

# 检查矩阵是否满足条件：有6个不同的冠军（且都是A-F）
def check_matrix(rankings):
    """
    检查矩阵是否满足条件
    :param rankings: 3x8的矩阵
    :return: bool
    """
    champions = calculate_champions(rankings)
    # 检查是否有6个不同的冠军
    if len(set(champions)) != 6:
        return False
    # 检查是否都是A-F（索引0-5）
    for champion in champions:
        if champion > 5:
            return False
    return True

# 生成所有符合条件的矩阵并检查
def exhaustive_search():
    """
    穷举所有符合条件的矩阵：
    1. 科目X固定为[1,2,3,4,5,6,7,8]
    2. 科目Y是1-8的排列，且科目Y中H（索引7）的排名为8
    3. 科目Z是1-8的排列，且科目Z中G（索引6）或H（索引7）的排名为8
    """
    # 科目X固定
    subject_X = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 生成所有可能的科目Y：1-8的排列，且第8位（索引7）是8
    # 即生成前7个位置的排列，然后在第8位放8
    count_Y = 0
    for perm_Y in itertools.permutations(range(1, 8)):
        count_Y += 1
        # 构建科目Y：前7个元素是perm_Y，第8个元素是8
        subject_Y = list(perm_Y) + [8]
        
        # 生成所有可能的科目Z：1-8的排列，且第7位（索引6）或第8位（索引7）是8
        count_Z = 0
        # 情况1：科目Z中H（索引7）的排名为8
        for perm_Z in itertools.permutations(range(1, 8)):
            count_Z += 1
            # 构建科目Z：前7个元素是perm_Z，第8个元素是8
            subject_Z = list(perm_Z) + [8]
            
            # 构建排名矩阵
            rankings = [subject_X, subject_Y, subject_Z]
            
            # 检查矩阵是否满足条件
            if check_matrix(rankings):
                print("找到符合条件的矩阵！")
                print(f"科目X: {subject_X}")
                print(f"科目Y: {subject_Y}")
                print(f"科目Z: {subject_Z}")
                champions = calculate_champions(rankings)
                print(f"6个科目顺序对应的冠军: {champions}")
                return True
            
            # 每处理一定数量的矩阵，输出进度
            if count_Z % 100000 == 0:
                print(f"已处理科目Y: {count_Y}, 科目Z情况1: {count_Z}")
        
        # 情况2：科目Z中G（索引6）的排名为8，H（索引7）的排名不是8
        for perm_Z in itertools.permutations(range(1, 8)):
            count_Z += 1
            # 构建科目Z：前6个元素是perm_Z[0:6]，第7个元素是8，第8个元素是perm_Z[6]
            subject_Z = list(perm_Z[0:6]) + [8] + [perm_Z[6]]
            
            # 构建排名矩阵
            rankings = [subject_X, subject_Y, subject_Z]
            
            # 检查矩阵是否满足条件
            if check_matrix(rankings):
                print("找到符合条件的矩阵！")
                print(f"科目X: {subject_X}")
                print(f"科目Y: {subject_Y}")
                print(f"科目Z: {subject_Z}")
                champions = calculate_champions(rankings)
                print(f"6个科目顺序对应的冠军: {champions}")
                return True
            
            # 每处理一定数量的矩阵，输出进度
            if count_Z % 100000 == 0:
                print(f"已处理科目Y: {count_Y}, 科目Z情况2: {count_Z}")
        
        # 每处理完一个科目Y，输出进度
        print(f"已处理科目Y: {count_Y}")
        print(f"  总处理矩阵数: {count_Y * count_Z}")
    
    print("没有找到符合条件的矩阵")
    return False

# 主函数
if __name__ == "__main__":
    print("开始穷举所有符合条件的矩阵...")
    print("科目X固定为: [1, 2, 3, 4, 5, 6, 7, 8]")
    print("科目Y要求: 1-8的排列，且H的排名为8")
    print("科目Z要求: 1-8的排列，且G或H的排名为8")
    print("=" * 60)
    
    found = exhaustive_search()
    
    if found:
        print("\n结论：存在6个不同冠军的情况！")
    else:
        print("\n结论：不存在6个不同冠军的情况！")
        print("潜在冠军的最大可能数量小于6")