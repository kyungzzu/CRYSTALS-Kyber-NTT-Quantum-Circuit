from projectq import MainEngine
from projectq.ops import H, CNOT, Measure, Toffoli, X, All, Swap, math
from projectq.backends import CircuitDrawer, ResourceCounter, CommandPrinter, ClassicalSimulator
from projectq.meta import Loop, Compute, Uncompute, Control, Dagger
from projectq.libs.math import AddConstant, AddConstantModN, MultiplyByConstantModN, SubConstant, SubConstantModN
# from projectq.libs.math._quantummath import add_quantum
# from kyber_zetas import *
import random

test_input = [
    2, 1, 1, 1, 0, 0, 0, 1, 2, 1,
    1, 0, 0, 2, -1, 2, 2, 2, 0, 1,
    1, -1, -2, 1, -1, 1, -2, 1, 1, -1,
    0, 0, 1, 0, 0, 0, 0, -1, 1, 0,
    0, 1, -1, 1, -1, 0, 0, 0, 2, 0,
    0, -1, 3, -1, 0, 0, -2, 0, 1, 0,
    -2, 3, -2, 1, 0, 0, 1, -2, 0, 2,
    0, 1, 1, 1, -2, -2, 2, 2, -2, 0,
    0, 0, 0, 1, 0, 3, -1, 1, 0, -1,
    -2, 0, 1, 1, 0, 3, -1, 1, -2, -1,
    -1, 0, -1, 0, 0, 2, 2, 1, -2, 1,
    1, -1, 0, -2, 0, -1, 2, 0, 0, -1,
    -1, 1, 1, -1, 0, 1, 0, 1, 2, 1,
    -2, 0, 0, 1, 1, -1, 2, -1, 0, 1,
    -2, 0, -1, -2, -2, 1, 2, 0, -1, 1,
    0, 0, 0, 0, 0, 2, -1, 1, 1, 0,
    1, -2, 0, 0, 0, -2, 2, 1, 0, 0,
    0, -1, -2, 0, 1, 0, 0, 0, 1, 0,
    -3, 1, 0, 1, -2, -1, -1, -1, -1, 0,
    0, -1, 0, 1, 0, 0, -1, -1, 0, 3,
    1, -1, -2, 1, 0, 2, 1, 1, 0, -1,
    -1, 0, 1, -1, -1, 0, 0, -1, -2, 1,
    -3, 1, 0, -2, 0, -2, 1, -1, 0, 0,
    0, 0, 1, -1, -1, 0, 2, -1, 1, -2,
    1, -2, 0, 1, 0, 0, -1, -1, -1, 0,
    0, 1, -2, -1, 1, -2
]


zetas = [-1044, -758, -359, -1517, 1493, 1422, 287, 202,
         -171, 622, 1577, 182, 962, -1202, -1474, 1468,
         573, -1325, 264, 383, -829, 1458, -1602, -130,
         -681, 1017, 732, 608, -1542, 411, -205, -1571,
         1223, 652, -552, 1015, -1293, 1491, -282, -1544,
         516, -8, -320, -666, -1618, -1162, 126, 1469,
         -853, -90, -271, 830, 107, -1421, -247, -951,
         -398, 961, -1508, -725, 448, -1065, 677, -1275,
         -1103, 430, 555, 843, -1251, 871, 1550, 105,
         422, 587, 177, -235, -291, -460, 1574, 1653,
         -246, 778, 1159, -147, -777, 1483, -602, 1119,
         -1590, 644, -872, 349, 418, 329, -156, -75,
         817, 1097, 603, 610, 1322, -1285, -1465, 384,
         -1215, -136, 1218, -1335, -874, 220, -1187, -1659,
         -1185, -1530, -1278, 794, -1510, -854, -870, 478,
         -108, -308, 996, 991, 958, -1460, 1522, 1628 ]


# use reduce
MONT = -1044
QINV = -3327

# NTT parameter
KYBER_N = 256
KYBER_Q = 3329


def classictoquantum(eng, const, q):
    for i in range(len(q)):
        if (const & 1 == 1):
            X | q[i]
        const = const >> 1

def MAJ(eng, a, b, c):
    # c0 = a0 xor c
    CNOT | (a, c)
    # b0 = a0 xor b0
    CNOT | (a, b)
    # a0 = a0 toffoli B0, C0
    Toffoli | (b, c, a)


def UMA(eng, a, b, c):
    Toffoli | (c, b, a)
    CNOT | (a, c)
    CNOT | (c, b)


def ripple_adder(eng, a, b, c0):
    z = eng.allocate_qubit()
    result = []
    MAJ(eng, a[0], b[0], c0)
    for i in range(len(a) - 1):
        MAJ(eng, a[(i + 1) % len(a)], b[(i + 1) % len(a)], a[(0 + i) % len(a)])
    b0 = len(b) - 1
    b1 = (len(b) - (len(b) - len(a))) - 1
    with Control(eng, b[b0:b1]):
        with Control(eng, a[len(a) - 1]):
            X | z
    for i in range(len(a) - 1):
        UMA(eng, a[((len(a) - 1) - i) % len(a)], b[((len(a) - 1) - i) % len(a)], a[(len(a) - 1 - 1 - i) % len(a)])
    UMA(eng, a[0], b[0], c0)

    for i in range(len(b)):
        result.append(b[i])
    result.append(z)
    b = result


def not_ripple_carry_add(eng, a, b, c0):
    MAJ(eng, a[0], b[0], c0)
    for i in range(len(a) - 1):
        MAJ(eng, a[(i + 1) % len(a)], b[(i + 1) % len(a)], a[(0 + i) % len(a)])
    # CNOT | (a[len(a)-1], b[len(a)])
    for i in range(len(a) - 1):
        UMA(eng, a[((len(a) - 1) - i) % len(a)], b[((len(a) - 1) - i) % len(a)], a[(len(a) - 1 - 1 - i) % len(a)])
    UMA(eng, a[0], b[0], c0)


def FFM1(eng, r, temp1, c, k, n):
    for i in range(len(r)):
        CNOT | (r[i], temp1[i])

    if zetas[k] != 1:
        if zetas[k] < 0:
            if test_input[n] > 0:
                for i in range(-zetas[k] + 1):
                    with Dagger(eng):
                        ripple_adder(eng, r, temp1, c)
            else:
                for i in range(-zetas[k] - 1):
                    ripple_adder(eng, r, temp1, c)
        else:
            if test_input[n] > 0:
                for i in range(zetas[k] - 1):
                    ripple_adder(eng, r, temp1, c)
            else:
                for i in range(zetas[k] + 1):
                    with Dagger(eng):
                        ripple_adder(eng, r, temp1, c)



def FFM2(eng, r, temp1, c, k, check):
    with Control(eng, r[len(r) - 1]):
        X | check

    for i in range(len(r) - 1):
        CNOT | (r[i], temp1[i])

    if zetas[k] != 1:
        if zetas[k] < 0:
            X | check
            with Control(eng, check):
                for i in range(-zetas[k] + 1):
                    with Dagger(eng):
                        ripple_adder(eng, r, temp1, c)
            X | check
            with Control(eng, check):
                for i in range(-zetas[k] - 1):
                    ripple_adder(eng, r, temp1, c)

        else:
            X | check
            with Control(eng, check):
                for i in range(zetas[k] - 1):
                    ripple_adder(eng, r, temp1, c)
            X | check

            with Control(eng, check):
                for i in range(zetas[k] + 1):
                    with Dagger(eng):
                        ripple_adder(eng, r, temp1, c)

        # check reset
        CNOT | (r[len(r) - 1], check)


def montgomery_reduction(eng, a, tmp, tmp_final, c):
    for i in range(-QINV):  # QINV: -3327
        with Dagger(eng):
            not_ripple_carry_add(eng, a[0:16], tmp[0:16], c)

    add = eng.allocate_qureg(16)

    for i in range(16):
        CNOT | (tmp[15], add[i])

    tmp = tmp[0:16] + add

    for i in range(KYBER_Q):
        not_ripple_carry_add(eng, tmp, tmp_final, c)

    with Dagger(eng):
        not_ripple_carry_add(eng, tmp_final, a, c)

    return a[16:32]


def NTT_sub1(eng, a, t, c):
    add = eng.allocate_qureg(16)
    for i in range(len(add)):
        CNOT | (t[len(t)-1], add[i])
    t = t + add

    not_ripple_carry_add(eng, t, a, c)

def NTT_sub2(eng, a, t, c):
    add = eng.allocate_qureg(16)
    for i in range(len(add)):
        CNOT | (t[len(t)-1], add[i])
    t = t+add

    with Dagger(eng):
        not_ripple_carry_add(eng, t, a, c)


def temp_save(eng, a, t):
    for i in range(len(a)):
        CNOT | (a[i], t[i])



def SWAP_final(eng, a, b):
    for i in range(len(a)):
        Swap | (a[i], b[i])


# main function
def Kyber_NTT(eng, n):
    for i in range(n):
        globals()['r' + str(i)] = eng.allocate_qureg(32)
    for j in range(n):
        for i in range(int(n / 2)):
            globals()['t' + str(i) + str(j)] = eng.allocate_qureg(32)
            globals()['mont_a' + str(i) + str(j)] = eng.allocate_qureg(16)
            globals()['mont_a2' + str(i) + str(j)] = eng.allocate_qureg(32)
            globals()['a_temp' + str(i) + str(j)] = eng.allocate_qureg(32)

    c = eng.allocate_qubit()  # c : ripple_carry
    check = eng.allocate_qubit()

    # Set test input
    for i in range(n):
        classictoquantum(eng, test_input[i], globals()['r' + str(i)])

    lenn = int(n / 2)
    k = 1
    j = 0
    N = 0

    while lenn >= 2:
        start = 0
        while start < n:
            for j in range(start, start + lenn, 1):
                if N == 0:
                    FFM1(eng, globals()['r' + str(j + lenn)], globals()['t' + str(k) + str(j)], c, k, j+lenn)
                else:
                    FFM2(eng, globals()['r' + str(j + lenn)], globals()['t' + str(k) + str(j)], c, k, check)

                globals()['mont_a' + str(k) + str(j)] = montgomery_reduction(eng, globals()['t' + str(k) + str(j)],
                                                                          globals()['mont_a' + str(k) + str(j)],
                                                                          globals()['mont_a2' + str(k) + str(j)], c)

                temp_save(eng, globals()['r' + str(j)], globals()['a_temp' + str(k) + str(j)])

                NTT_sub2(eng, globals()['a_temp' + str(k) + str(j)], globals()['mont_a' + str(k) + str(j)], c)
                NTT_sub1(eng, globals()['r' + str(j)], globals()['mont_a' + str(k) + str(j)], c)

                SWAP_final(eng, globals()['r' + str(j + lenn)], globals()['a_temp' + str(k) + str(j)])
            N = N + 1
            k = k + 1
            start = j + 1 + lenn
        lenn >>= 1
        print("k")
        print(k)


Resource = ResourceCounter()
eng = MainEngine(Resource)
Kyber_NTT(eng, 16)
print(Resource)
