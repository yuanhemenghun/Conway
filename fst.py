from typing import Protocol, Iterable, Mapping
from collections import defaultdict, deque
from itertools import permutations, product


EPSILON = ""
ENDMARK = "#"


class Hashable(Protocol):
    def __eq__(self, value: object, /) -> bool:
        return super().__eq__(value)
    def __hash__(self) -> int:
        return super().__hash__()


class FST[T: Hashable]:
    def __init__(self, trans: Iterable[tuple[T, str, str, T]], start: T, finals: Iterable[T]) -> None:
        graph: defaultdict[T, dict[str, tuple[T, str]]] = defaultdict(dict)
        for frm, inpt, output, to in trans:
            graph[frm][inpt] = (to, output)
            if to not in graph:
                graph[to] = {}

        self.graph, self.start, self.finals = dict(graph), start, frozenset(finals)

    @staticmethod
    def directly_build[_T: Hashable](graph: Mapping[_T, Mapping[str, tuple[_T, str]]], start: _T, finals: Iterable[_T]):
        fst = FST([], start, finals)
        fst.graph = {frm: {inpt: to_output for inpt, to_output in paths.items()} for frm, paths in graph.items()}
        return fst

    def __call__(self, inpt: str | None) -> str | None:
        if inpt is None:
            return None
        state = self.start
        result: list[str] = []
        for i in range(len(inpt)):
            trans = self.graph[state].get(inpt[i])
            if trans is None:
                return
            state, output = trans
            result.append(output)
        if state not in self.finals:
            return None
        return "".join(result)

    def __eq__(self, value: object) -> bool:
        if not isinstance(value, self.__class__):
            return False
        self_que = deque([self.start])
        other_que = deque([value.start])
        self_map_other = {self.start: value.start}
        while self_que:
            self_state = self_que.popleft()
            other_state = other_que.popleft()
            self_paths, other_paths = self.graph[self_state], value.graph[other_state]
            if len(self_paths) != len(other_paths):
                return False
            for inpt, (self_next_state, self_output) in self_paths.items():
                if inpt not in other_paths:
                    return False
                other_next_state, other_output = other_paths[inpt]
                self_is_final, other_is_final = self_next_state in self.finals, other_next_state in value.finals
                if self_output != other_output or self_is_final is not other_is_final:
                    return False
                if self_next_state in self_map_other:
                    if other_next_state != self_map_other[self_next_state]:
                        return False
                    continue
                self_que.append(self_next_state)
                other_que.append(other_next_state)
                self_map_other[self_next_state] = other_next_state
        return True

    @property
    def status(self):
        return list(self.graph)

    def zip_status_to_int(self):
        status_to_int: dict[T, int] = {}
        for i, state in enumerate(self.graph):
            status_to_int[state] = i

        new_graph: defaultdict[int, dict[str, tuple[int, str]]] = defaultdict(dict)
        for state, paths in self.graph.items():
            new_paths = new_graph[status_to_int[state]]
            for inpt, (next_state, output) in paths.items():
                new_paths[inpt] = (status_to_int[next_state], output)
        return self.directly_build(new_graph, status_to_int[self.start], (status_to_int[state] for state in self.finals))

    def as_DFA(self):
        result: defaultdict[T, dict[str, T]] = defaultdict(dict)
        for state, paths in self.graph.items():
            dfa_paths = result[state]
            for inpt, (next_state, _) in paths.items():
                dfa_paths[inpt] = next_state
        return dict(result)


def compose[B, A](before: FST[B], after: FST[A]):
    graph: defaultdict[tuple[B, A], dict[str, tuple[tuple[B, A], str]]] = defaultdict(dict)
    start = (before.start, after.start)
    finals = frozenset((before_state, after_state) for before_state, after_state in product(before.finals, after.finals))

    # 初步复合
    que = deque([start])
    while que:
        before_state, after_state = que.popleft()
        if (before_state, after_state) in graph:
            continue
        paths = graph[before_state, after_state]
        before_paths = before.graph[before_state]
        after_paths = after.graph[after_state]
        for before_input, (next_before_state, temp) in before_paths.items():
            next_after_paths, next_after_state, total_output = after_paths, after_state, EPSILON
            for c in temp:
                after_tran = next_after_paths.get(c)
                if after_tran is None:
                    break
                next_after_state, output = after_tran
                total_output += output
                next_after_paths = after.graph[next_after_state]
            else:
                paths[before_input] = ((next_before_state, next_after_state), total_output)
                que.append((next_before_state, next_after_state))

    # 构建反向图，用于一些图上操作
    reverse_graph: defaultdict[tuple[B, A], set[tuple[tuple[B, A], str]]] = defaultdict(set)
    for state, paths in graph.items():
        for inpt, (next_state, _) in paths.items():
            reverse_graph[next_state].add((state, inpt))
        if state not in reverse_graph:
            reverse_graph[state]
    all_status = list(graph)

    def set_trans_to(frm: tuple[B, A], inpt: str, new_to: tuple[B, A]):
        old_to, output = graph[frm][inpt]
        reverse_graph[old_to].remove((frm, inpt))
        graph[frm][inpt] = (new_to, output)
        reverse_graph[new_to].add((frm, inpt))

    def del_state(state: tuple[B, A]):
        next_paths, prev_paths = graph[state], reverse_graph[state]
        for inpt, (next_state, _) in next_paths.items():
            reverse_graph[next_state].remove((state, inpt))
        for prev_state, inpt in prev_paths:
            del graph[prev_state][inpt]
        del graph[state], reverse_graph[state]

    # 移除到不了可接受状态的状态
    able_visit_final: set[tuple[B, A]] = set()
    que = deque(finals)
    while que:
        state = que.popleft()
        if state in able_visit_final:
            continue
        able_visit_final.add(state)
        for next_state, _ in reverse_graph[state]:
            que.append(next_state)

    for state in all_status:
        if state not in able_visit_final:
            del_state(state)
    del able_visit_final

    # 最小化
    belong_block: dict[tuple[B, A], int] = {state: 0 for state in graph if state not in finals} | {state: 1 for state in finals}
    blocks: defaultdict[tuple[tuple[str, str, int], ...], set[tuple[B, A]]] = defaultdict(set)
    block_num, new_block_num = -1, 0
    while new_block_num > block_num:
        block_num = new_block_num
        blocks.clear()
        for state in graph:
            trans: list[tuple[str, str, int]] = []
            for inpt, (next_state, output) in graph[state].items():
                trans.append((inpt, output, belong_block[next_state]))
            trans.sort()
            blocks[tuple(trans)].add(state)
        for i, same_block_status in enumerate(blocks.values()):
            for state in same_block_status:
                belong_block[state] = i
        new_block_num = len(blocks)

    remain_status: list[tuple[B, A]] = [start] * new_block_num
    for same_block_status in blocks.values():
        remain_state = same_block_status.pop()
        remain_status[belong_block[remain_state]] = remain_state

    for remain_state in remain_status:
        for inpt, (next_state, output) in graph[remain_state].items():
            remain_next_state = remain_status[belong_block[next_state]]
            set_trans_to(remain_state, inpt, remain_next_state)
    for same_block_status in blocks.values():
        for state in same_block_status:
            del_state(state)

    return FST.directly_build(graph, start, finals).zip_status_to_int()


if __name__ == "__main__":
    CHARS = ("1", "2", "3", "d")
    EX_CHARS = CHARS + ("⋄",)
    MAX_COUNT = 3
    audio_trans = (
        [("start", ENDMARK, EPSILON, "end")] +  # 允许只有终止符（空串）
        [("start", c, EPSILON, f"1{c}") for c in CHARS] +  # 从初始读入第一个字符
        [(f"{count}{c}", c, EPSILON, f"{count + 1}{c}") for count in range(1, MAX_COUNT) for c in CHARS] +  # 读入相同字符
        [(f"{count}{c1}", c2, f"{count}{c1}", f"1{c2}") for count in range(1, MAX_COUNT + 1) for c1, c2 in permutations(CHARS, 2)] +  # 读入不同字符
        [(f"{count}{c}", ENDMARK, f"{count}{c}{ENDMARK}", f"end") for count in range(1, MAX_COUNT + 1) for c in CHARS]  # 读入终止符
    )
    audio = FST(audio_trans, "start", ["end"])

    exlarge_audio_trans = (
        audio_trans +
        [(f"{count}{c}", "⋄", f"{count}{c}", f"{c}⋄") for count in range(1, MAX_COUNT + 1) for c in CHARS] +  # 从计数状态读入分裂符，记忆分裂符前的最后一个字符
        [(f"{c1}⋄", c2, "⋄", f"1{c2}") for c1, c2 in permutations(CHARS, 2)] +  # 从分裂符状态读入与分裂符前面不同字符（不接受相同字符）
        [(f"{c}⋄", "⋄", "⋄", f"{c}⋄") for c in CHARS] +  # 允许连续⋄组
        [("start", "⋄", "⋄", "start")] + [(f"{c}⋄", ENDMARK, f"⋄{ENDMARK}", f"end") for c in CHARS]  # 以分裂符开始和以分裂符结束
    )
    exlarge_audio = FST(exlarge_audio_trans, "start", ["end"])

    sink = FST([("start", c, EPSILON, "start") for c in EX_CHARS] + [("start", ENDMARK, EPSILON, "end")], "start", ["end"])

    from time import time

    start = time()

    _ex = exlarge_audio.zip_status_to_int()
    last_s_ex = sink
    s_ex = compose(_ex, sink)
    i = 1
    print(i, len(_ex.status), len(s_ex.status))
    while last_s_ex != s_ex:
        last_s_ex = s_ex
        i += 1
        _ex = compose(_ex, exlarge_audio)
        s_ex = compose(_ex, sink)
        print(i, len(_ex.status), len(s_ex.status))

    end = time()
    print(f"{end - start = }")

    stable_sink_exlarge_audio = s_ex
    print(stable_sink_exlarge_audio.as_DFA())

    """
    {
        0: {'1': 6, '2': 21, '3': 20, 'd': 19, '⋄': 0},
        1: {},
        2: {'1': 3, '3': 10, 'd': 12, '⋄': 2, '#': 1},
        3: {'1': 14, '2': 17, '3': 7, 'd': 5},
        4: {'d': 5},
        5: {'1': 6, '2': 21, '3': 20, '#': 1, '⋄': 5},
        6: {'1': 9, '2': 21, '3': 20, 'd': 19, '#': 1, '⋄': 11},
        7: {'1': 6, '2': 21, 'd': 19, '#': 1, '⋄': 11},
        8: {'2': 21, '3': 20, 'd': 19, '#': 1, '⋄': 11},
        9: {'1': 8, '2': 21, '3': 20, 'd': 19, '#': 1, '⋄': 11},
        10: {'1': 9, '2': 13, 'd': 16, '#': 1, '⋄': 11},
        11: {'2': 18, '⋄': 11, '#': 1},
        12: {'d': 4, '1': 6, '2': 21, '3': 20, '#': 1, '⋄': 5},
        13: {'2': 17, '1': 6, '3': 20, 'd': 19, '#': 1, '⋄': 2},
        14: {'1': 8},
        15: {'3': 7, '1': 6, '2': 21, 'd': 19, '#': 1, '⋄': 11},
        16: {'d': 5, '1': 6, '2': 21, '3': 20, '#': 1, '⋄': 5},
        17: {'1':6, '3': 20, 'd': 19, '#': 1, '⋄': 2},
        18: {'2': 2},
        19: {'d': 16, '1': 6, '2': 21, '3': 20, '#': 1, '⋄': 5},
        20: {'3': 15, '1': 6, '2': 21, 'd': 19, '#': 1, '⋄': 11},
        21: {'2': 13, '1': 6, '3': 20, 'd': 19, '#': 1, '⋄': 2}
    }
    """

