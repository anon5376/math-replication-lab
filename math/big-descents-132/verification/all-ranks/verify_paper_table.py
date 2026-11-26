"""Compare literal enumeration with Table 2 of arXiv:2408.15111v2 (ranks 0 through 9)."""
from itertools import combinations, permutations

TABLE_2 = [
    [1], [1], [2], [3, 2], [4, 9, 1],
    [5, 25, 12], [6, 55, 64, 7], [7, 105, 233, 82, 2],
    [8, 182, 674, 505, 61], [9, 294, 1668, 2206, 660, 25],
]


def literal_row(n):
    triples = list(combinations(range(n), 3))
    row = [0] * (n + 1)
    for word in permutations(range(n)):
        if any(word[i] < word[k] < word[j] for i, j, k in triples):
            continue
        big_descents = sum(a > b + 1 for a, b in zip(word, word[1:]))
        row[big_descents] += 1
    while row and row[-1] == 0:
        row.pop()
    return row


for n, published in enumerate(TABLE_2):
    row = literal_row(n)
    if row != published:
        raise ValueError((n, row, published))
    print(n, row)
print("All ten literal rows equal Table 2.")
