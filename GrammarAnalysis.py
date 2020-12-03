#!/usr/bin/env python3.6.5
# -*- coding: UTF-8 -*-
"""
Author: 徐运哲
Date: 2020/11/5 14:24
docs:

"""

from LexicalAnalysis import LexicalScanner


class SLRAnalyzer:
    def __init__(self, start, new_start='S', point='.', sharp='$', acc='acc'):
        self.start = start
        self.productions = {
            'Program': [['Header', 'Function']],
            'Header': [['127', '47', '220', '48', '222', 'Header_']],
            'Header_': [['Header'], ['null']],
            'Parameter': [['DataType', '0'], ['DataType', '0', 'Parameter'], ['46']],
            'ReturnType': [['2'], ['13'], ['24'], ['46']],
            'FunctionName': [['0'], ['1']],
            'Function': [
                ['ReturnType', 'FunctionName', '121', 'Parameter', '122', '125', 'FunctionBody', '126', 'Function_']],
            'Function_': [['Function'], ['null']],
            # 改动
            'FunctionBody': [['VariableDef', 'ProcessStc', 'ReturnStc']],
            'ReturnStc': [['33', '0', '124'], ['33', 'Num', '124']],
            'VariableDef': [['DataType', '0', '124', 'VariableDef_']],
            'VariableDef_': [['VariableDef'], ['null']],
            'DataType': [['2'], ['24'], ['13']],
            'ProcessStc': [['S', 'ProcessStc_']],
            # 改动
            'S': [['AssignmentStc', '124'], ['JudgeStc'], ['LoopStc'], ['FunctionCall', '124']],
            'ProcessStc_': [['ProcessStc'], ['null']],
            'AssignmentStc': [['0', '226', 'C']],
            'C': [['0'], ['Num'], ['Operate']],
            # 改动
            'Operate': [['0', 'Operator', 'Num'], ['Num', 'Operator', 'Num'], ['0', '211'], ['0', '214']],
            'Operator': [['210'], ['213'], ['216'], ['218']],
            'JudgeStc': [['3', '121', 'Condition', '122', '125', 'ProcessStc', '126', 'E']],
            'E': [['4', '125', 'ProcessStc', '126'], ['null']],
            'Condition': [['0', 'JudgeOperator', '0'], ['0', 'JudgeOperator', 'Num'],
                          ['Num', 'JudgeOperator', 'Num'], ['Num'], ['0']],
            'JudgeOperator': [['225'], ['222'], ['220'], ['223'], ['221'], ['224']],
            'LoopStc': [['5', '121', 'Condition', '122', '125', 'ProcessStc', '126'],
                        ['19', '121', 'Condition', '122', '5', '125', 'ProcessStc', '126'],
                        ['6', '121', 'AssignmentStc', '124', 'Condition', '124', 'Operate', '122', '125', 'ProcessStc',
                         '126']],
            # 改动
            'FunctionCall': [['0', '226', 'FunctionName', '121', '0', '122'], ['FunctionName', 'Parameter']],
            'Num': [['300'], ['301']]
        }
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

    def get_terminal_symbols(self):
        for non_terminal_symbol in self.non_terminal_symbols:
            for production in self.productions[non_terminal_symbol]:
                for item in production:
                    if item not in self.non_terminal_symbols:
                        self.terminal_symbols.add(item)
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
                            # 若下一个符号是非终结符，那么则将它first集中除空串之外的元素加到当前非终结符的follow集中
                            else:
                                for item in self.first[production[i + 1]]:
                                    if item != 'null':
                                        self.follow[production[i]].add(item)
                        # 如果A是某个句型的最右符号，则将结束符添加到FOLLOW(A)
                        # else:
                        #     self.follow[production[i]].add(self.sharp)
                    # 任何一个终结符，如果可以紧跟着A出现，那么该终结符也可以紧跟着B出现
                    for j in range(0, length):
                        real = length - j - 1
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
        print('follow', self.follow)

    def init_naive_productions(self):
        self.naive_productions.append((self.new_start, [self.start]))
        for symbol in self.non_terminal_symbols:
            for production in self.productions[symbol]:
                self.naive_productions.append((symbol, production))

    def get_closure_old(self, production_set):
        old_production_set = production_set.copy()
        # 直到闭包不再增大为止
        while True:
            # for J中每一个形如B  α.Aβ的项目
            for production in production_set:
                right = production[1]
                point_index = right.index(self.point)
                if point_index == len(right) - 1 or right[point_index + 1] in self.terminal_symbols:
                    continue
                else:
                    # for G’中每一个形如Aγ的产生式 do
                    for production_ in self.productions[right[point_index + 1]]:
                        right_ = production_.copy()
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
                else:
                    # for G’中每一个形如Aγ的产生式 do
                    for production_ in self.productions[right[point_index + 1]]:
                        right_ = production_.copy()
                        # 如果产生式B  α.Aβ中A可以推出空串，则将B  αA.β加入闭包
                        if right_ == ['null']:
                            original_right = right.copy()
                            original_right.remove(self.point)
                            original_right.insert(point_index + 1, self.point)
                            result = (production[0], original_right)
                        else:
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

    # 构造slr(1)分析表
    def build_analysis_table(self):
        initial_status = [(self.new_start, [self.point, self.start])]
        closure = self.get_closure(initial_status)
        self.status_list.append(closure)
        # 计算完初始状态的闭包，开始基于初始状态构造分析表（状态转换图）
        self.change_status(closure, 0)
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

    def analyze_grammar_old(self, code):
        status_stack = [0]
        symbol_stack = [self.sharp]
        code.append(self.sharp)
        pointer = 0
        while True:
            action = self.action[status_stack[-1]][code[pointer]]
            if action == '':
                return False
            if action == self.acc:
                return True
            if action[0] == 's':
                status_stack.append(action[1])
                symbol_stack.append(code[pointer])
                pointer += 1
            elif action[0] == 'r':
                left = self.naive_productions[action[1]][0]
                right = self.naive_productions[action[1]][1]
                for i in range(0, len(right)):
                    status_stack.pop()
                    if symbol_stack.pop() != right[len(right) - i - 1]:
                        raise Exception('wrong!')
                print('归约产生式：', self.naive_productions[action[1]])
                symbol_stack.append(left)
                status_stack.append(self.goto[status_stack[-1]][left])

    def analyze_grammar(self, code):
        status_stack = [0]
        symbol_stack = [self.sharp]
        code.append((self.sharp, self.sharp))
        pointer = 0
        while True:
            tmp = code[pointer][0]
            action = self.action[status_stack[-1]][str(tmp)]
            if action == '':
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
            if action[0] == 's':
                status_stack.append(action[1])
                symbol_stack.append(str(code[pointer][0]))
                pointer += 1
            elif action[0] == 'r':
                left = self.naive_productions[action[1]][0]
                right = self.naive_productions[action[1]][1]
                for i in range(0, len(right)):
                    if symbol_stack[-1] != right[len(right) - i - 1]:
                        if self.check_can_be_null(right[len(right) - i - 1]):
                            pass
                        else:
                            raise Exception('文法有误！')
                    else:
                        status_stack.pop()
                        symbol_stack.pop()
                print('归约产生式：', self.naive_productions[action[1]])
                symbol_stack.append(left)
                status_stack.append(self.goto[status_stack[-1]][left])

    def check_can_be_null(self, symbol):
        if symbol in self.non_terminal_symbols and 'null' in self.first[symbol]:
            return True
        else:
            return False


if __name__ == '__main__':
    # productions = {
    #     # 'Program': [['Header', 'Function']],
    #     # 'Header': [['#', 'include', '<', 'iostream', '>', 'Header_']],
    #     # 'Header_': [['Header'], ['null']],
    #     # 'Parameter': [['DataType', 'Variable'], ['DataType', 'Variable', 'Parameter'], ['void']],
    #     # 'ReturnType': [['int'], ['char'], ['float'], ['void']],
    #     # 'FunctionName': [['Variable']],
    #     # 'Function': [['ReturnType', 'FunctionName', '{', 'FunctionBody', '}'],
    #     #              ['ReturnType', 'FunctionName', '{', 'FunctionBody', '}', 'Function_']],
    #     # 'Function_': [['Function'], ['null']],
    #     # 'FunctionBody': [['VariableDef'], ['ProcessStc'], ['ReturnStc']],
    #     # 'ReturnStc': [['return', 'Variable'], ['return', 'Num']],
    #     # 'VariableDef': [['DataType', 'Variable', ';', 'VariableDef_']],
    #     # 'VariableDef_': [['VariableDef'], ['null']],
    #     # 'DataType': [['int'], ['float'], ['char']],
    #     # 'ProcessStc': [['S', 'ProcessStc_']],
    #     # 'S': [['AssignmentStc'], ['JudgeStc'], ['LoopStc'], ['FunctionCall']],
    #     # 'ProcessStc_': [['ProcessStc'], ['null']],
    #     # 'AssignmentStc': [['Variable', '=', 'C']],
    #     # 'C': [['Variable', 'Num', 'Operate']],
    #     # 'Operate': [['Variable', 'Operator', 'Num'], ['Num', 'Operator', 'Num']],
    #     # 'Operator': [['+'], ['-'], ['*'], ['/']],
    #     # 'JudgeStc': [['if', '(', 'Condition', ')', '{', 'ProcessStc', '}', 'E']],
    #     # 'E': [['else', '{', 'ProcessStc', '}'], ['null']],
    #     # 'Condition': [['Variable', 'JudgeOperator', 'Variable'], ['Variable', 'JudgeOperator', 'Num'],
    #     #               ['Num', 'JudgeOperator', 'Num'], ['Num'], ['Variable']],
    #     # 'JudgeOperator': [['=='], ['>'], ['<'], ['>='], ['<='], ['!=']],
    #     # 'LoopStc': [['while', '(', 'Condition', ')', '{', 'ProcessStc', '}'],
    #     #          ['do', '(', 'Condition', ')', 'while', '{', 'ProcessStc', '}'],
    #     #          ['for', '(', 'AssignmentStc', ';', 'Condition', ';', 'Operate', ')', '{', 'ProcessStc', '}']],
    #     # 'FunctionCall': [['Variable', '=', 'FunctionName', '(', 'Parameter', ')', ';'], ['FunctionName', ['Parameter']]]
    #
    #     'A': [['V', '=', 'E']],
    #     'E': [['E', '+', 'T'], ['E', '-', 'T'], ['T']],
    #     'T': [['T', '*', 'F'], ['T', '/', 'F'], ['F']],
    #     'F': [['(', 'E', ')'], ['i']],
    #     'V': [['i']],
    # }
    scanner = LexicalScanner('main.c')
    analyzer = SLRAnalyzer('Program')
    # test = [('VariableDef', ['DataType', '0', '124', '.', 'VariableDef_'])]
    # print(analyzer.get_closure(test))
    print(analyzer.analyze_grammar(scanner.lexical_analysis()))
