import itertools
import random

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

# 生成更有针对性的随机排名矩阵
def generate_targeted_rankings():
    """
    生成更有针对性的随机排名矩阵，让学生0-5在不同科目中交替排名靠前
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 生成科目1的排名：让学生0-3排名1-4，学生4-5排名5-6，学生6-7排名7-8
    subject1 = list(range(1, 7)) + random.sample([7, 8], 2)
    # 确保学生0-3的排名在前4
    top4_in_subject1 = random.sample(range(6), 4)
    rank_list = list(range(1, 5)) + list(range(5, 7))
    subject1 = [0]*8
    for i in range(4):
        subject1[top4_in_subject1[i]] = rank_list[i]
    for i in range(8):
        if subject1[i] == 0:
            subject1[i] = rank_list.pop(0)
    
    # 生成科目2的排名：让学生0-3排名1-4，学生4-5排名5-6，学生6-7排名7-8
    subject2 = list(range(1, 7)) + random.sample([7, 8], 2)
    # 确保学生0-3的排名在前4，但与科目1的前4学生不完全相同
    top4_in_subject2 = random.sample(range(6), 4)
    rank_list = list(range(1, 5)) + list(range(5, 7))
    subject2 = [0]*8
    for i in range(4):
        subject2[top4_in_subject2[i]] = rank_list[i]
    for i in range(8):
        if subject2[i] == 0:
            subject2[i] = rank_list.pop(0)
    
    return [subject0, subject1, subject2]

# 构造一个更平衡的矩阵，让每个学生在至少一个科目中排名前2
def construct_balanced_matrix():
    """
    构造一个平衡的排名矩阵，让学生0-5在不同科目中排名前2
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生0和1排名前2，学生2和3排名3-4，学生4和5排名5-6
    subject1 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目2：学生2和3排名前2，学生4和5排名3-4，学生0和1排名5-6
    subject2 = [5, 6, 1, 2, 3, 4, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个让学生4和5也能成为潜在冠军的矩阵
def construct_include_4_5():
    """
    构造一个排名矩阵，让学生4和5在至少一个科目中排名前4，有机会通过第一轮淘汰
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生4和5排名前4，学生0和1排名5-6，学生2和3排名3-4
    subject1 = [5, 6, 3, 4, 1, 2, 7, 8]
    
    # 科目2：学生4和5排名前4，学生0和1排名3-4，学生2和3排名5-6
    subject2 = [3, 4, 5, 6, 1, 2, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个非常特殊的矩阵，让学生4和5在特定科目顺序中成为冠军
def construct_special_for_4_5():
    """
    构造一个特殊的排名矩阵，让学生4和5在特定科目顺序中成为冠军
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生4和5排名前2，学生0和1排名3-4，学生2和3排名5-6
    subject1 = [3, 4, 5, 6, 1, 2, 7, 8]
    
    # 科目2：学生4和5排名前2，学生2和3排名3-4，学生0和1排名5-6
    subject2 = [5, 6, 3, 4, 1, 2, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个让学生5也能成为潜在冠军的矩阵
def construct_include_5():
    """
    构造一个排名矩阵，让学生5在科目1和科目2中排名前4，有机会成为潜在冠军
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生5和4排名前2，学生2和3排名3-4，学生0和1排名5-6
    subject1 = [5, 6, 3, 4, 2, 1, 7, 8]
    
    # 科目2：学生5和4排名前2，学生0和1排名3-4，学生2和3排名5-6
    subject2 = [3, 4, 5, 6, 2, 1, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个让学生0-5都有可能成为潜在冠军的矩阵
def construct_all_6():
    """
    构造一个复杂的排名矩阵，让学生0-5都有可能成为潜在冠军
    :return: 3x8的排名矩阵
    """
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生0-5排名1-6，学生6-7排名7-8
    subject1 = [1, 3, 5, 2, 4, 6, 7, 8]
    
    # 科目2：学生0-5排名1-6，学生6-7排名7-8
    subject2 = [2, 4, 6, 1, 3, 5, 7, 8]
    
    return [subject0, subject1, subject2]

# 构造一个特定的排名矩阵
def construct_target_rankings():
    """
    构造一个特定的排名矩阵，尝试让学生0-5都成为潜在冠军
    :return: 3x8的排名矩阵
    """
    # 科目0：学生0-7依次排名1-8（固定）
    subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
    
    # 科目1：学生0-5的排名为1-6，学生6-7的排名为7-8
    subject1 = [2, 4, 1, 5, 3, 6, 7, 8]
    
    # 科目2：学生0-5的排名为1-6，学生6-7的排名为7-8
    subject2 = [3, 1, 4, 2, 6, 5, 7, 8]
    
    return [subject0, subject1, subject2]

# 智能搜索最佳排名矩阵
def search_best_rankings(iterations=100000):
    """
    智能搜索最佳排名矩阵，寻找最大的潜在冠军数量（仅考虑学生0-5）
    :param iterations: 搜索迭代次数
    :return: (最大潜在冠军数量, 对应的排名矩阵, 潜在冠军学生集合, 各科目顺序对应的冠军)
    """
    max_count = 0
    max_champions = set()
    max_rankings = None
    max_order_champions = {}
    
    for i in range(iterations):
        # 使用新的有针对性的生成函数
        if i % 2 == 0:
            rankings = generate_targeted_rankings()
        else:
            # 完全随机生成，但确保学生6和7排名靠后
            subject0 = [1, 2, 3, 4, 5, 6, 7, 8]
            subject1 = random.sample(range(1, 9), 8)
            subject2 = random.sample(range(1, 9), 8)
            # 确保学生6和7在科目1和科目2中排名5-8
            while subject1[6] <= 4 or subject1[7] <= 4 or subject2[6] <= 4 or subject2[7] <= 4:
                subject1 = random.sample(range(1, 9), 8)
                subject2 = random.sample(range(1, 9), 8)
            rankings = [subject0, subject1, subject2]
        
        count, champions, order_champions = count_potential_champions(rankings)
        
        # 只考虑学生0-5作为潜在冠军
        valid_champions = champions - {6, 7}
        valid_count = len(valid_champions)
        
        if valid_count > max_count:
            max_count = valid_count
            max_champions = valid_champions
            max_rankings = rankings
            max_order_champions = order_champions
            print(f"迭代 {i}: 找到新的最大值: {max_count}")
            print(f"潜在冠军学生: {max_champions}")
            print(f"各科目顺序对应的冠军: {max_order_champions}")
            print(f"排名矩阵:")
            for j in range(3):
                print(f"科目{j}: {max_rankings[j]}")
            print()
            
            # 如果找到6个潜在冠军，直接返回
            if max_count == 6:
                return max_count, max_rankings, max_champions, max_order_champions
    
    return max_count, max_rankings, max_champions, max_order_champions

# 测试一个特定的排名矩阵
def test_specific_rankings(rankings, name):
    """
    测试一个特定的排名矩阵，输出潜在冠军数量和每个科目顺序对应的冠军
    """
    print(f"\n测试{name}的排名矩阵：")
    # 计算潜在冠军数量
    count, champions, order_champions = count_potential_champions(rankings)
    valid_champions = champions - {6, 7}
    valid_count = len(valid_champions)
    
    print(f"总潜在冠军数量: {count}")
    print(f"有效潜在冠军数量(A-F): {valid_count}")
    print(f"有效潜在冠军学生: {valid_champions}")
    
    # 输出每个科目顺序对应的冠军
    for subject_order in itertools.permutations([0, 1, 2]):
        champion = order_champions[subject_order]
        print(f"科目顺序 {subject_order} 对应的冠军是学生 {champion}")

# 主函数
if __name__ == "__main__":
    # 测试手动构造的排名矩阵
    test_specific_rankings(construct_target_rankings(), "目标构造")
    test_specific_rankings(construct_balanced_matrix(), "平衡构造")
    
    # 构造一个更复杂的矩阵，尝试让多个学生成为潜在冠军
    complex_matrix = [
        [1, 2, 3, 4, 5, 6, 7, 8],  # 科目0
        [3, 1, 4, 2, 5, 6, 8, 7],  # 科目1
        [2, 4, 1, 3, 6, 5, 7, 8]   # 科目2
    ]
    test_specific_rankings(complex_matrix, "复杂构造")
    
    # 测试包含4和5的矩阵
    test_specific_rankings(construct_include_4_5(), "包含4和5的构造")
    test_specific_rankings(construct_special_for_4_5(), "专为4和5设计的构造")
    test_specific_rankings(construct_include_5(), "包含5的构造")
    test_specific_rankings(construct_all_6(), "包含0-5的构造")
    
    # 智能搜索最佳排名矩阵
    print("\n智能搜索最佳排名矩阵（仅考虑A-F）：")
    max_count, max_rankings, max_champions, max_order_champions = search_best_rankings(iterations=100000)
    
    print(f"\n最终结果：")
    print(f"最大有效潜在冠军数量(A-F): {max_count}")
    print(f"潜在冠军学生: {max_champions}")
    print(f"各科目顺序对应的冠军: {max_order_champions}")
    print(f"对应的排名矩阵:")
    for i in range(3):
        print(f"科目{i}: {max_rankings[i]}")