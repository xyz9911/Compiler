#!/usr/bin/env python3.6.5
# -*- coding: UTF-8 -*-
"""
Author: 徐运哲
Date: 2020/11/16 18:09
docs:

"""

from LexicalAnalysis import LexicalScanner


class NodeInfo:
    def __init__(self):
        self.name = ''
        self.val = ''
        self.quad = ''  # 指令标号
        self.width = 0
        self.type = ''
        self.trueList = []
        self.falseList = []
        self.nextList = []
        self.code = ''


class StackNode:
    def __init__(self, symbol):
        self.symbol = symbol
        self.info = NodeInfo()


# tmp_count = 0
# code = []
#
#
# def gen_code(str):
#     code.append(str)
#
#
# def gen_math_code(right_tmp):
#     left = right_tmp[2].info.name
#     op = right_tmp[1].info.name
#     right = right_tmp[0].info.name
#     tmp_count += 1
#     code.append('t' + tmp_count + '=' + left + ' ' + op + '' + right)
#
#
# # 创建一个只包含i的列表，i是跳转指令的标号，函数返回指向新创建列表的指针
# def make_list(i):
#     pass
#
#
# # 将p1和p2指向的列表进行合并，指向合并后列表的指针
# def merge(list_1, list_2):
#     tmp = list_1.union(list_2)
#     return tmp
#
#
# # 将i作为目标标号插入到p所指列表的各指令中
# def back_patch(list, addr):
#     for item in list:
#         code[item] += addr


# 将p1和p2指向的列表进行合并，指向合并后列表的指针
def merge(list_1, list_2):
    tmp = list_1.union(list_2)
    return tmp


class SemanticAnalyzer:
    def __init__(self, start, new_start='S', point='.', sharp='$', acc='acc', log_level=0):
        self.start = start
        self.productions = {
            'Program': [['Header', 'Function']],
            'Header': [['127', '47', '220', '48', '222', 'Header_']],
            'Header_': [['Header'], ['null']],
            'Parameter': [['DataType', '0', 'Action:allocateParam', '123', 'Parameter_'], ['46']],
            'Parameter_': [['Parameter'], ['null']],
            'Action:allocateParam': [['null', 'do:allocateParam']],
            'ReturnType': [['2', 'do:passReturnType'], ['13', 'do:passReturnType'], ['24', 'do:passReturnType'], ['46', 'do:passReturnType']],
            'FunctionName': [['0', 'do:passFunctionName'], ['1']],
            'Function': [
                ['ReturnType', 'FunctionName', 'Action:allocateFunc', '121', 'Parameter', '122', '125', 'FunctionBody',
                 '126', 'Function_']],
            'Action:allocateFunc': [['null', 'do:allocateFunc']],
            'Function_': [['Function'], ['null']],
            # 改动
            'FunctionBody': [['VariableDef', 'ProcessStc', 'ReturnStc']],
            'ReturnStc': [['33', '0', '124', 'do:returnVariable'], ['33', 'Num', '124', 'do:returnNum']],
            'VariableDef': [['DataType', '0', 'Action:allocateVar', '124', 'VariableDef_']],
            'Action:allocateVar': [['null', 'do:allocateVar']],
            'VariableDef_': [['VariableDef'], ['null']],
            'DataType': [['2', 'do:typeInt'], ['24', 'do:typeFloat'], ['13', 'do:typeChar']],
            'ProcessStc': [['S', 'ProcessStc_']],
            # 改动
            'S': [['AssignmentStc', '124'], ['JudgeStc'], ['LoopStc'], ['FunctionCall', '124']],
            'ProcessStc_': [['ProcessStc'], ['null']],
            'AssignmentStc': [['0', '226', 'C', 'do:passValueToVar']],
            'C': [['0', 'do:passVarValue'], ['Num', 'do:passNumValue'], ['Operate', 'do:passTmpValue']],
            # 改动
            'Operate': [['0', 'Operator', 'Num', 'do:operateVarNum'], ['Num', 'Operator', 'Num', 'do:operateVarVar'],
                        ['0', '211'],
                        ['0', '214']],
            'Operator': [['210', 'do:+'], ['213', 'do:-'], ['216', 'do:*'], ['218', 'do:/']],
            'JudgeStc': [['3', '121', 'Condition', '122', '125', 'Action:backPatchTrue', 'ProcessStc', '126',
                          'Action:backPatchFalse', 'E']],
            'Action:backPatchTrue': [['null', 'do:backPatchTrue']],
            'Action:backPatchFalse': [['null', 'do:backPatchFalse']],
            'E': [['4', '125', 'ProcessStc', '126', 'do:backPatchElse'], ['null']],
            'Condition': [['0', 'JudgeOperator', '0', 'do:VarVar'],
                          ['0', 'JudgeOperator', 'Num', 'do:VarNum'],
                          ['Num', 'JudgeOperator', 'Num', 'do:NumNum'], ['Num', 'do:Num'],
                          ['0', 'do:Var']],
            'JudgeOperator': [['225', 'do:=='], ['222', 'do:>'], ['220', 'do:<'],
                              ['223', 'do:>='], ['221', 'do:<='], ['224', 'do:!=']],
            'LoopStc': [
                ['5', '121', 'Condition', '122', '125', 'Action:backPatchTrue', 'ProcessStc', '126', 'do:goBack']
                # ['19', '121', 'Condition', '122', '5', '125', 'ProcessStc', '126'],
                # ['6', '121', 'AssignmentStc', '124', 'Condition', '124', 'Operate', '122', '125', 'ProcessStc',
                #  '126']
                ],
            # 改动
            'FunctionCall': [['0', '226', 'FunctionName', '121', '0', '122'], ['FunctionName', 'Parameter']],
            'Num': [['300', 'do:assignInt'], ['301', 'do:assignFloat']]
        }
        self.log_level = log_level
        self.naive_productions = []
        self.new_start = new_start
        self.point = point
        self.sharp = sharp
        self.acc = acc
        self.non_terminal_symbols = self.productions.keys()
        self.terminal_symbols = set()
        self.get_terminal_symbols()
        self.init_naive_productions()
        self.first = {non_terminal_symbol: set() for non_terminal_symbol in self.non_terminal_symbols}
        self.follow = {non_terminal_symbol: set() for non_terminal_symbol in self.non_terminal_symbols}
        self.get_first()
        self.get_follow()
        self.status_list = []
        terminal_symbols_ = self.terminal_symbols.copy()
        terminal_symbols_.add(self.sharp)
        self.action = [{item: '' for item in terminal_symbols_} for i in range(200)]
        self.goto = [{item: '' for item in self.non_terminal_symbols} for i in range(200)]
        self.build_analysis_table()
        self.offset = 0
        self.tmp_count = 0
        self.code = []
        self.symbol_table = {}

    def get_terminal_symbols(self):
        for non_terminal_symbol in self.non_terminal_symbols:
            for production in self.productions[non_terminal_symbol]:
                for item in production:
                    if item not in self.non_terminal_symbols and item[0] != 'd':
                        self.terminal_symbols.add(item)
        if self.log_level > 0:
            print('terminal symbols:', self.terminal_symbols)

    # 递归一次计算完所有涉及元素的first集
    def _get_first(self, non_terminal_symbol):
        for production in self.productions[non_terminal_symbol]:
            if production[0] in self.terminal_symbols:
                self.first[non_terminal_symbol].add(production[0])
            elif production[0] == non_terminal_symbol:
                continue
            else:
                # 如果已经计算过该非终结符的first集，则跳过
                if not self.first[production[0]]:
                    self._get_first(production[0])
                for first in self.first[production[0]]:
                    # 将该非终结符first集中所有非空串的终结符添加到当前分析的非终结符first集中
                    if first != 'null':
                        self.first[non_terminal_symbol].add(first)
                    else:
                        # 遍历当前产生式，若之后每个字符的first集都存在空串，再把空串加到当前分析的非终结符first集中
                        for symbol in production:
                            # 如果已经计算过该非终结符的first集，则跳过
                            if not self.first[symbol]:
                                self._get_first(symbol)
                            if 'null' not in self.first[symbol]:
                                break
                            self.first[non_terminal_symbol].add(first)

    def get_first(self):
        for non_terminal_symbol in self.non_terminal_symbols:
            # 如果已经计算过该非终结符的first集，则跳过
            if not self.first[non_terminal_symbol]:
                self._get_first(non_terminal_symbol)
        if self.log_level > 0:
            print('first:', self.first)

    def get_follow(self):
        old_follow = self.follow.copy()
        self.follow[self.start].add(self.sharp)
        # 直到follow集不再变动为止
        while True:
            for non_terminal_symbol in self.non_terminal_symbols:
                for production in self.productions[non_terminal_symbol]:
                    length = len(production)
                    for i in range(0, length):
                        if production[i] in self.terminal_symbols:
                            continue
                        # 对于当前产生式中最后一个符号以前的符号
                        elif i < length - 1:
                            # 若下一个符号是终结符，那么直接将它加到这个非终结符的follow集中
                            if production[i + 1] in self.terminal_symbols:
                                self.follow[production[i]].add(production[i + 1])
                            # 若下一个是动作，则跳过
                            elif production[i + 1][0] == 'd':
                                continue
                            # 若下一个符号是非终结符，那么则将它first集中除空串之外的元素加到当前非终结符的follow集中
                            else:
                                for item in self.first[production[i + 1]]:
                                    if item != 'null' and item[0] != 'd':
                                        self.follow[production[i]].add(item)
                        # 如果A是某个句型的最右符号，则将结束符添加到FOLLOW(A)
                        # else:
                        #     self.follow[production[i]].add(self.sharp)
                    # 任何一个终结符，如果可以紧跟着A出现，那么该终结符也可以紧跟着B出现
                    for j in range(0, length):
                        real = length - j - 1
                        if production[real][0] == 'd':
                            continue
                        if j == 0 and production[real] in self.non_terminal_symbols:
                            self.follow[production[real]] = self.follow[production[real]].union(
                                self.follow[non_terminal_symbol])
                            continue
                        elif production[real] in self.non_terminal_symbols and ('null' in self.first[production[real]]):
                            continue
                        elif production[real] in self.terminal_symbols:
                            break
                        self.follow[production[real]] = self.follow[production[real]].union(
                            self.follow[non_terminal_symbol])
                        break
            if old_follow == self.follow:
                break
            else:
                old_follow = self.follow.copy()
        if self.log_level > 0:
            print('follow', self.follow)

    def init_naive_productions(self):
        self.naive_productions.append((self.new_start, [self.start]))
        for symbol in self.non_terminal_symbols:
            for production in self.productions[symbol]:
                self.naive_productions.append((symbol, production))

    def get_closure(self, production_set):
        old_production_set = production_set.copy()
        # 直到闭包不再增大为止
        while True:
            # for J中每一个形如B  α.Aβ的项目
            for production in production_set:
                right = production[1]
                point_index = right.index(self.point)
                if point_index == len(right) - 1 or right[point_index + 1] in self.terminal_symbols:
                    continue
                elif right[point_index + 1][0] == 'd':
                    right.remove(self.point)
                    right.insert(point_index + 1, self.point)
                else:
                    # for G’中每一个形如Aγ的产生式 do
                    for production_ in self.productions[right[point_index + 1]]:
                        right_ = production_.copy()
                        # 如果产生式B  α.Aβ中A可以推出空串，则将B  αA.β加入闭包
                        # if right_[0] == 'null':
                        #     original_right = right.copy()
                        #     original_right.remove(self.point)
                        #     original_right.insert(point_index + 1, self.point)
                        #     result = (production[0], original_right)
                        #     right_copy = right_.copy()
                        #     right_copy.append(self.point)
                        #     result_2 = (right[point_index + 1], right_copy)
                        #     print(result_2)
                        #     if result_2 not in production_set:
                        #         production_set.append(result_2)
                        # else:
                        right_.insert(0, self.point)
                        result = (right[point_index + 1], right_)
                        # if A  .γ不在C中,将A  .γ加入J中
                        if result not in production_set:
                            production_set.append(result)
            if old_production_set == production_set:
                break
            else:
                old_production_set = production_set.copy()
        return production_set

    # 构造slr(1)分析
    def build_analysis_table(self):
        initial_status = [(self.new_start, [self.point, self.start])]
        closure = self.get_closure(initial_status)
        self.status_list.append(closure)
        # 计算完初始状态的闭包，开始基于初始状态构造分析表（状态转换图）
        self.change_status(closure, 0)
        if self.log_level > 0:
            print('status:')
            for item in self.status_list:
                print(item)

    # 开始递归构造分析表以及状态表
    def change_status(self, status, status_id):
        # 构造一个字典存储可能由该状态衍生的其他状态
        possible_new_status = {symbol: [] for symbol in self.terminal_symbols.union(self.non_terminal_symbols)}
        for production in status:
            right = production[1].copy()
            point_index = right.index(self.point)
            # 若句点在产生式的最后一个位置，进行规约操作，构造action表的R元素
            if point_index == len(right) - 1:
                right.remove(self.point)
                if (production[0], right) == self.naive_productions[0]:
                    self.action[status_id][self.sharp] = self.acc
                else:
                    index = self.naive_productions.index((production[0], right))
                    follow = self.follow[production[0]]
                    for key in self.action[status_id].keys():
                        if key in follow:
                            self.action[status_id][key] = ('r', index)
                continue
            # 若在中间位置，则计算闭包，将结果添加到字典可能的状态中，注意是添加操作，取并集！
            else:
                forward_char = right[point_index + 1]
                right.remove(self.point)
                right.insert(point_index + 1, self.point)
                if forward_char[0] == 'd':
                    continue
                closure = self.get_closure([(production[0], right)])
                for pro in closure:
                    if pro not in possible_new_status[forward_char]:
                        possible_new_status[forward_char].append(pro)
        # 检验可能由该状态衍生出的其他状态
        for symbol in self.terminal_symbols.union(self.non_terminal_symbols):
            if len(possible_new_status[symbol]) == 0:
                continue
            else:
                # 若没有该状态，新创建一个状态，再将编号填入action或goto表中。
                if possible_new_status[symbol] not in self.status_list:
                    self.status_list.append(possible_new_status[symbol])
                    id = len(self.status_list) - 1
                    self.change_status(possible_new_status[symbol], id)
                # 若先前状态表中已存在该状态，那么寻找那个状态的编号，将它填入action或goto表中。
                else:
                    id = self.status_list.index(possible_new_status[symbol])
                if symbol in self.terminal_symbols:
                    self.action[status_id][symbol] = ('s', id)
                else:
                    self.goto[status_id][symbol] = id

    def analyze_grammar(self, code):
        status_stack = [0]
        symbol_stack = [self.sharp]
        code.append((self.sharp, self.sharp))
        pointer = 0
        while True:
            tmp = code[pointer][0]
            action = self.action[status_stack[-1]][str(tmp)]
            null_action = self.action[status_stack[-1]]['null']
            if action == '' and null_action == '':
                print('Grammar Exception when analyzing symbol:', code[pointer])
                expects = []
                for key in self.action[status_stack[-1]].keys():
                    if self.action[status_stack[-1]][key] != '':
                        expects.append(key)
                print('expect symbol: ', expects)
                print('symbol location:', pointer)
                print(code[:pointer + 1])
                print('current status stack:', status_stack)
                print('current symbol stack:', symbol_stack)
                return False
            if action == self.acc:
                return True
            if action == '' and null_action[0] == 's':
                status_stack.append(null_action[1])
                new_node = StackNode(('null', 'null'))
                symbol_stack.append(new_node)
            elif action[0] == 's':
                status_stack.append(action[1])
                new_node = StackNode(code[pointer])
                symbol_stack.append(new_node)
                pointer += 1
            # elif null_action[0] == 's':
            #     status_stack.append(null_action[1])
            #     new_node = StackNode('null')
            #     symbol_stack.append(new_node)
            elif action[0] == 'r':
                left = self.naive_productions[action[1]][0]
                right = self.naive_productions[action[1]][1]
                for i in range(0, len(right)):
                    tmp = symbol_stack[-1].symbol[0]
                    # 假如产生式右部符号不在符号栈中，那么有两种情况，该右部符号可以为空串，或该右部符号是一个动作，应当执行
                    if str(symbol_stack[-1].symbol[0]) != right[len(right) - i - 1]:
                        current_symbol = right[len(right) - i - 1]
                        if current_symbol[0] == 'd':
                            self.semantic_action(symbol_stack, current_symbol)
                        # 该右部符号可以为空串，那么可以忽略该符号继续归约，但不要忘了，这个可推出空串非终结符归约时也有可能有具体动作！
                        # elif current_symbol == 'null':
                        #     status_stack.pop()
                        else:
                            raise Exception('文法有误！')
                    else:
                        status_stack.pop()
                        symbol = symbol_stack.pop()
                if self.log_level > 0:
                    print('归约产生式：', self.naive_productions[action[1]])
                # new_node = StackNode(left)
                symbol.symbol = (left, 0)
                symbol_stack.append(symbol)
                status_stack.append(self.goto[status_stack[-1]][left])

    def check_can_be_null(self, symbol):
        if symbol in self.non_terminal_symbols and 'null' in self.first[symbol]:
            return True
        else:
            return False

    def semantic_action(self, symbol_stack, action):
        if action == 'do:allocateParam':
            pass
        elif action == 'do:passFunctionName':
            pass
        elif action == 'do:allocateFunc':
            if symbol_stack[-2].info.name == '':
                pass
        elif action == 'do:passReturnType':
            symbol_stack[-1].info.type = symbol_stack[-1].symbol[1]
        elif action == 'do:returnVariable':
            if symbol_stack[-2].symbol[1] not in self.symbol_table.keys():
                print('undefined variable:' + symbol_stack[-3].symbol[1])
            else:
                symbol_stack[-2].info.type = self.symbol_table[symbol_stack[-2].symbol[1]][0]
                if symbol_stack[-12].info.type != symbol_stack[-2].info.type:
                    print('variable type not match')
                else:
                    self.gen_code('return ' + symbol_stack[-2].symbol[1])
        elif action == 'do:returnNum':
            if symbol_stack[-12].info.type != symbol_stack[-2].info.type:
                print('variable type not match')
            else:
                self.gen_code('return ' + symbol_stack[-2].info.val)
        elif action == 'do:allocateVar':
            name = symbol_stack[-2].symbol[1]
            type = symbol_stack[-3].info.type
            width = symbol_stack[-3].info.width
            self.symbol_table[name] = (type, self.offset, 0)
            self.offset += width
        elif action == 'do:typeInt':
            symbol_stack[-1].info.type = 'int'
            symbol_stack[-1].info.width = 4
        elif action == 'do:typeFloat':
            symbol_stack[-1].info.type = 'float'
            symbol_stack[-1].info.width = 4
        elif action == 'do:typeChar':
            symbol_stack[-1].info.type = 'char'
            symbol_stack[-1].info.width = 1
        elif action == 'do:passValueToVar':
            if symbol_stack[-3].symbol[1] not in self.symbol_table.keys():
                print('undefined variable:' + symbol_stack[-3].symbol[1])
            else:
                symbol_stack[-3].info.type = self.symbol_table[symbol_stack[-3].symbol[1]][0]
                if symbol_stack[-1].info.type != symbol_stack[-3].info.type:
                    print('variable type not match')
                else:
                    symbol_stack[-3].info.val = symbol_stack[-1].info.val
                    self.symbol_table[symbol_stack[-3].symbol[1]] = (
                        self.symbol_table[symbol_stack[-3].symbol[1]][0],
                        self.symbol_table[symbol_stack[-3].symbol[1]][1],
                        symbol_stack[-3].info.val)
                    self.gen_code(symbol_stack[-3].symbol[1] + '=' + str(symbol_stack[-1].info.name))

        elif action == 'do:passVarValue':
            symbol_stack[-1].info.name = symbol_stack[-1].symbol[1]
        elif action == 'do:passNumValue':
            symbol_stack[-1].info.name = symbol_stack[-1].info.val
        elif action == 'do:passTmpValue':
            symbol_stack[-1].info.name = 't' + str(self.tmp_count)
        elif action == 'do:operateVarNum':
            if symbol_stack[-3].symbol[1] not in self.symbol_table.keys():
                print('undefined variable:' + symbol_stack[-3].symbol[1])
            else:
                symbol_stack[-3].info.type = self.symbol_table[symbol_stack[-3].symbol[1]][0]
                if symbol_stack[-1].info.type != symbol_stack[-3].info.type:
                    print('variable type not match')
                else:
                    self.tmp_count += 1
                    self.gen_code(
                        't' + str(self.tmp_count) + '=' + symbol_stack[-3].symbol[1] + symbol_stack[-2].info.name + str(
                            symbol_stack[-1].info.val))
        elif action == 'do:operateVarVar':
            if symbol_stack[-3].symbol[1] not in self.symbol_table.keys() or symbol_stack[-1].symbol[1]:
                print('undefined variable:' + symbol_stack[-3].symbol[1])
            else:
                symbol_stack[-3].info.type = self.symbol_table[symbol_stack[-3].symbol[1]][0]
                symbol_stack[-1].info.type = self.symbol_table[symbol_stack[-1].symbol[1]][0]
                if symbol_stack[-1].info.type != symbol_stack[-3].info.type:
                    print('variable type not match')
                else:
                    self.tmp_count += 1
                    self.gen_code(
                        't' + str(self.tmp_count) + '=' + symbol_stack[-3].symbol[1] + symbol_stack[-2].info.name +
                        symbol_stack[-1].symbol[1])
        elif action == 'do:+':
            symbol_stack[-1].info.name = '+'
        elif action == 'do:-':
            symbol_stack[-1].info.name = '-'
        elif action == 'do:*':
            symbol_stack[-1].info.name = '*'
        elif action == 'do:/':
            symbol_stack[-1].info.name = '/'
        elif action == 'do:backPatchTrue':
            current_cursor = len(self.code)
            self.back_patch(symbol_stack[-4].info.trueList, current_cursor)
        elif action == 'do:backPatchFalse':
            current_cursor = len(self.code)
            self.gen_code('goto ')
            symbol_stack[-7].info.nextList.append(current_cursor)
            current_cursor = len(self.code)
            self.back_patch(symbol_stack[-7].info.falseList, current_cursor)
        elif action == 'do:backPatchElse':
            current_cursor = len(self.code)
            self.back_patch(symbol_stack[-11].info.nextList, current_cursor)
        elif action == 'do:VarVar':
            if symbol_stack[-3].symbol[1] not in self.symbol_table.keys():
                print('undefined variable:' + symbol_stack[-3].symbol[1])
            elif symbol_stack[-1].symbol[1] not in self.symbol_table.keys():
                print('undefined variable:' + symbol_stack[-1].symbol[1])
            else:
                symbol_stack[-3].info.type = self.symbol_table[symbol_stack[-3].symbol[1]][0]
                symbol_stack[-1].info.type = self.symbol_table[symbol_stack[-1].symbol[1]][0]
                if symbol_stack[-1].info.type != symbol_stack[-3].info.type:
                    print('variable type not match')
                else:
                    self.gen_code(
                        'if ' + symbol_stack[-3].symbol[1] + symbol_stack[-2].info.name + symbol_stack[-1].symbol[
                            1] + ' goto')
                    self.gen_code('goto ')
                    current_cursor = len(self.code)
                    symbol_stack[-3].info.quad = current_cursor - 2
                    symbol_stack[-3].info.trueList.append(current_cursor - 2)
                    symbol_stack[-3].info.falseList.append(current_cursor - 1)
        elif action == 'do:VarNum':
            if symbol_stack[-3].symbol[1] not in self.symbol_table.keys():
                print('undefined variable:' + symbol_stack[-3].symbol[1])
            else:
                symbol_stack[-3].info.type = self.symbol_table[symbol_stack[-3].symbol[1]][0]
                if symbol_stack[-1].info.type != symbol_stack[-3].info.type:
                    print('variable type not match')
                else:
                    self.gen_code('if ' + symbol_stack[-3].symbol[1] + symbol_stack[-2].info.name + str(
                        symbol_stack[-1].info.val) + ' goto')
                    self.gen_code('goto ')
                    current_cursor = len(self.code)
                    symbol_stack[-3].info.quad = current_cursor - 2
                    symbol_stack[-3].info.trueList.append(current_cursor - 2)
                    symbol_stack[-3].info.falseList.append(current_cursor - 1)
        elif action == 'do:==':
            symbol_stack[-1].info.name = '=='
        elif action == 'do:>':
            symbol_stack[-1].info.name = '>'
        elif action == 'do:<':
            symbol_stack[-1].info.name = '<'
        elif action == 'do:>=':
            symbol_stack[-1].info.name = '>='
        elif action == 'do:<=':
            symbol_stack[-1].info.name = '<='
        elif action == 'do:!=':
            symbol_stack[-1].info.name = '!='
        elif action == 'do:goBack':
            self.gen_code('goto ' + str(symbol_stack[-6].info.quad))
            current_cursor = len(self.code)
            self.back_patch(symbol_stack[-6].info.falseList, current_cursor)
        elif action == 'do:assignInt':
            symbol_stack[-1].info.type = 'int'
            symbol_stack[-1].info.val = int(symbol_stack[-1].symbol[1])
        elif action == 'do:assignFloat':
            symbol_stack[-1].info.type = 'float'
            symbol_stack[-1].info.val = float(symbol_stack[-1].symbol[1])
        if self.log_level > 0:
            print(action)

    def gen_code(self, str):
        self.code.append(str)

    def gen_math_code(self, symbol_stack):
        left = symbol_stack[-3].info.name
        op = symbol_stack[-2].info.name
        right = symbol_stack[-1].info.name
        self.tmp_count += 1
        self.code.append('t' + str(self.tmp_count) + '=' + left + ' ' + op + '' + right)

    # 创建一个只包含i的列表，i是跳转指令的标号，函数返回指向新创建列表的指针
    def make_list(self, i):
        pass

    # 将i作为目标标号插入到p所指列表的各指令中
    def back_patch(self, list, addr):
        for item in list:
            self.code[item] += str(addr)

    def output_code(self):
        for i in range(len(self.code)):
            print(i, ':', self.code[i])


if __name__ == '__main__':
    scanner = LexicalScanner('main.c')
    analyzer = SemanticAnalyzer('Program')
    print(analyzer.analyze_grammar(scanner.lexical_analysis()))
    analyzer.output_code()
