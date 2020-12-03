#!/usr/bin/env python3.6.5
# -*- coding: UTF-8 -*-
"""
Author: 徐运哲
Date: 2020/10/28 21:37
docs:

"""

Value = ["" for l in range(5)]
Reserve = ["" for i in range(60)]
Operator = ["" for j in range(230)]
Boundary = ["" for k in range(128)]


def init_value():
    Value[1] = "int"
    Value[2] = "float"


def init_reserve():
    Reserve[1] = "main"
    Reserve[2] = "int"
    Reserve[3] = "if"
    Reserve[4] = "else"
    Reserve[5] = "while"
    Reserve[6] = "for"
    Reserve[7] = "read"
    Reserve[8] = "write"
    Reserve[9] = "bool"
    Reserve[10] = "break"
    Reserve[11] = "case"
    Reserve[12] = "catch"
    Reserve[13] = "char"
    Reserve[14] = "class"
    Reserve[15] = "const"
    Reserve[16] = "continue"
    Reserve[17] = "default"
    Reserve[18] = "delete"
    Reserve[19] = "do"
    Reserve[20] = "double"
    Reserve[21] = "enum"
    Reserve[22] = "false"
    Reserve[23] = "true"
    Reserve[24] = "float"
    Reserve[25] = "friend"
    Reserve[26] = "goto"
    Reserve[27] = "inline"
    Reserve[28] = "long"
    Reserve[29] = "new"
    Reserve[30] = "private"
    Reserve[31] = "protected"
    Reserve[32] = "public"
    Reserve[33] = "return"
    Reserve[34] = "short"
    Reserve[35] = "signed"
    Reserve[36] = "sizeof"
    Reserve[37] = "static"
    Reserve[38] = "struct"
    Reserve[39] = "switch"
    Reserve[40] = "this"
    Reserve[41] = "try"
    Reserve[42] = "typedef"
    Reserve[43] = "unsigned"
    Reserve[44] = "using"
    Reserve[45] = "virtual"
    Reserve[46] = "void"
    Reserve[47] = "include"
    Reserve[48] = "iostream"
    Reserve[49] = "namespace"
    Reserve[50] = "std"
    # Reserve[51] = "printf"


def init_operator():
    Operator[210] = "+"
    Operator[211] = "++"
    Operator[212] = "+="
    Operator[213] = "-"
    Operator[214] = "--"
    Operator[215] = "-="
    Operator[216] = "*"
    Operator[217] = "*="
    Operator[218] = "/"
    Operator[219] = "/="
    Operator[220] = "<"
    Operator[221] = "<="
    Operator[222] = ">"
    Operator[223] = ">="
    Operator[224] = "!="
    Operator[225] = "=="
    Operator[226] = "="


def init_boundary():
    Boundary[121] = "("
    Boundary[122] = ")"
    Boundary[123] = ","
    Boundary[124] = ";"
    Boundary[125] = "{"
    Boundary[126] = "}"
    Boundary[127] = "#"


init_value()
init_reserve()
init_boundary()
init_operator()


class LexicalScanner:
    def __init__(self, file_name):
        self.symbol_table = set()
        self.split_results = []
        self.error_info = []
        with open(file_name, 'r') as f:
            for line in f.readlines():
                self.split_results.extend(line.split())
        self.result = []

    def lexical_analysis(self):
        for word in self.split_results:
            pointer = 0
            while pointer < len(word):
                char = word[pointer]

                if char == '(':
                    self.result.append((121, char))

                elif char == ')':
                    self.result.append((122, char))

                elif char == ',':
                    self.result.append((123, char))

                elif char == ';':
                    self.result.append((124, char))

                elif char == '{':
                    self.result.append((125, char))

                elif char == '}':
                    self.result.append((126, char))

                elif char == '#':
                    self.result.append((127, char))

                elif char == '+':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '+':
                            self.result.append((211, Operator[211]))
                            pointer = tmp_pointer + 1
                            continue
                        elif forward == '=':
                            self.result.append((212, Operator[212]))
                            pointer = tmp_pointer + 1
                            continue
                    self.result.append((210, Operator[210]))

                elif char == '-':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '-':
                            self.result.append((214, Operator[214]))
                            pointer = tmp_pointer + 1
                            continue
                        elif forward == '=':
                            self.result.append((215, Operator[215]))
                            pointer = tmp_pointer + 1
                            continue
                    self.result.append((213, Operator[213]))

                elif char == '*':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '=':
                            self.result.append((217, Operator[217]))
                            pointer = tmp_pointer + 1
                            continue
                    self.result.append((216, Operator[216]))

                elif char == '/':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '=':
                            self.result.append((219, Operator[219]))
                            pointer = tmp_pointer + 1
                            continue
                    self.result.append((218, Operator[218]))

                elif char == '>':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '=':
                            self.result.append((223, Operator[223]))
                            pointer = tmp_pointer + 1
                            continue
                    self.result.append((222, Operator[222]))

                elif char == '!':
                    tmp_pointer = pointer + 1
                    if tmp_pointer > len(word) - 1 or word[tmp_pointer] != '=':
                        self.result.append((-1, char))
                        pointer = tmp_pointer
                    else:
                        self.result.append((224, Operator[224]))
                        pointer = tmp_pointer

                elif char == '<':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '=':
                            self.result.append((221, Operator[221]))
                            pointer = tmp_pointer + 1
                            continue
                    self.result.append((220, Operator[220]))

                elif char == '=':
                    if pointer < len(word) - 1:
                        tmp_pointer = pointer + 1
                        forward = word[tmp_pointer]  # 缓冲区向前搜索一位，看看是不是两位运算符
                        if forward == '=':
                            self.result.append((225, Operator[225]))
                            pointer = tmp_pointer + 1
                            continue

                    self.result.append((226, Operator[226]))

                elif char.isdigit():
                    tmp_pointer = pointer
                    meet_dot = False
                    while tmp_pointer < len(word):
                        if word[tmp_pointer] == "." and not meet_dot:
                            tmp_pointer += 1
                            meet_dot = True
                            continue
                        if not word[tmp_pointer].isdigit():
                            break
                        tmp_pointer += 1
                    if meet_dot:
                        self.result.append((301, word[pointer:tmp_pointer]))
                    else:
                        self.result.append((300, word[pointer:tmp_pointer]))
                    pointer = tmp_pointer - 1

                elif char.isalpha():
                    tmp_pointer = pointer
                    while tmp_pointer < len(word):
                        if not word[tmp_pointer].isalpha():
                            break
                        tmp_pointer += 1
                    res = word[pointer:tmp_pointer]
                    pointer = tmp_pointer - 1
                    if res in Reserve:
                        self.result.append((Reserve.index(res), res))
                    else:
                        self.result.append((0, res))
                        self.symbol_table.add(res)

                else:
                    self.error_info.append(char)
                    self.result.append((-1, char))
                    break
                pointer += 1
        return self.result

    def print_error_info(self):
        if self.error_info:
            print("读取下列字符时出现了错误：")
            for item in self.error_info:
                print(item)
        else:
            print("没有发现错误")

    def print_symbol_table(self):
        print("符号表如下：")
        for item in self.symbol_table:
            print(item)


if __name__ == "__main__":
    test = LexicalScanner('main.c')
    print("")
    print(test.lexical_analysis())
    test.print_error_info()
    test.print_symbol_table()
