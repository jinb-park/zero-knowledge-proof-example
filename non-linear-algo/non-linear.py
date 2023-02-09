import numpy as np;

# Goal: implementing non-linear algorithm only through boolean and arithmetic circuits
#       so that we can take these algorithms to implement ZK circuits for non-linear functions
#       that are heavily used in ML.

# n is a number of elements that the output array contains.
# v is a number we want to turn it into a n-size array.
# e.g., n=5, v=6 --> [1, 0, 1, 0, 0, 0]
def num2bits(v, n):
    lc1 = 0
    e2 = 1
    res = list(np.zeros(shape=(n), dtype=np.int32))

    for i in range(n):
        res[i] = (v >> i) & 1
        assert(res[i] * (res[i] - 1) == 0)
        lc1 += res[i] * e2
        e2 = e2 + e2
    
    assert(lc1 == v)
    return res

# if v1 is less than v2, return 1. otherwise return 0
# how it works (intuition behind this logic)
# -- (0) basically, it is similar in concept to checking whether a subtraction carry happens.
# -- (1) v1 = 2 (010), v2 = 4 (100)
# -- (2) v1 - v2 --> 010 - 100 --> operations on the most significant bit (0 - 1) raises subtraction carry (-1)
#        but if it can accommodate only three bits, there is no space to propagate the carry.
#        so we need to get additional spaces to make that happen. (+ (1 << n)) is what actually does the job.
#        (simply assume n=4)
# -- (3) (v1 + (1 << 4)) --> 10010,  10010 - 00100 --> the subtraction carry occured at 2 can go all the way to the MSB.
# -- (4) (v1 + (1 << 4)) - v2 = 14 (01110) --> due to the carry applied, MSB will be 0 if v1 is less than v2. (otherwise, 1)
# -- (5) (1 - arr[n]) --> arr[n] indicates the MSB. (1 - arr[n]) will be 1 only if v1 is less than v2.
def less_than(v1, v2, n):
    v = v1 + (1 << n) - v2
    arr = num2bits(v, n+1)
    res = 1 - arr[n]
    return res

# check if v1 is greater than v2
def greater_than(v1, v2, n):
    return less_than(v2, v1, n)

# conditionally swap two values
# if sel is 0: no swap, return (v1, v2)
# if sel is 1: swap, return (v2, v1)
def swap(sel, v1, v2):
    aux = (v2 - v1) * sel
    return (aux + v1, -aux + v2)

def max(vals, n):
    length = len(vals)
    maxs = list(np.zeros(shape=(length+1), dtype=np.int32))
    maxs[0] = vals[0]

    for i in range(length):
        sel = greater_than(vals[i], maxs[i], n) # if val > max, sel will be set to 1
        v1, _ = swap(sel, maxs[i], vals[i]) # if sel == 1, v1 will be val (larger one)
        maxs[i+1] = v1                      # if sel == 0 (val <= max), v1 will be max
    return maxs[length]

def argmax(vals, n):
    length = len(vals)
    maxs = list(np.zeros(shape=(length+1), dtype=np.int32))
    amaxs = list(np.zeros(shape=(length+1), dtype=np.int32))  # for index
    maxs[0] = vals[0]
    amaxs[0] = 0

    for i in range(length):
        # for max
        sel = greater_than(vals[i], maxs[i], n)
        v1, _ = swap(sel, maxs[i], vals[i])
        maxs[i+1] = v1

        # for index
        v1, _ = swap(sel, amaxs[i], i)  # if sel == 1 (val > max), i should be max
        amaxs[i+1] = v1
    return amaxs[length]

# for is_negative(), I'll assume a finite field that has no negative value so it needs a way to encode and decode.
# if p=257, p-1=256, it can express the range of [-128,128]
def is_negative(v, p):
    d = (int)((p - 1) / 2)
    return greater_than(v, d, 10)

def relu(v, p):
    x = 1 - is_negative(v, p)  # if negative, x will be 0. oterwise 1.
    return x * v

if __name__ == "__main__":
    print(num2bits(5, 10))
    print(less_than(2, 4, 10))
    print(greater_than(2, 4, 10))
    print(swap(0, 2, 4))
    print(max([7,2,8,11,3], 10))
    print(argmax([7,2,13,11,3], 10))
    print(is_negative(255, 257))
    print(is_negative(5, 257))
    print(relu(255, 257))
    print(relu(5, 257))
    