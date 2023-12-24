# This is a part of a joint work by Luis Angel Gonzalez-Serrano and Egor Maximenko
# "Bialternant formula for Schur polynomials with repeating variables"

import time


def partitions_with_bounded_sum(summax):
    plist = []
    for w in range(summax + 1):
        plist += list(Partitions(w))
    return list(sorted(plist))


def partitions_with_bounded_length_and_bounded_sum(nmax, summax):
    plist = []
    for w in range(summax + 1):
        plist += list(Partitions(w, max_length = nmax))
    return list(sorted(plist))


def partitions_with_given_length_and_bounded_sum(n, summax):
    plist = []
    for w in range(summax + 1):
        plist += list(Partitions(w, length = n))
    return list(sorted(plist))


def pol_ring(letter, n):
    varnames = [letter + str(k) for k in range(n)]
    PR = PolynomialRing(QQ, varnames)
    return PR


def pol_vars(letter, n):
    return pol_ring(letter, n).gens()


# The Sage function 'det' crashes for some symbolic matrices.
# The following simple recursive version is more stable.
# Note that we do not create the submatrices explicitly.
# The sum over all permutations is slower because our matrices usually have many zeros.


def det_recur(A, rfirst, cols):
    if rfirst == A.nrows():
        return A.base_ring().one()
    result = A.base_ring().zero()
    s = 1
    for k in cols:
        if A[rfirst][k] != 0:
            newcols = [c for c in cols if c != k]
            result += A[rfirst][k] * det_recur(A, rfirst + 1, newcols) * s
        s = -s
    return result


def my_det(A):
    return det_recur(A, 0, list(range(A.nrows())))


def hom_polynomials(xs, degstop):
    n = len(xs)
    PR = parent(xs[0])
    hs = vector(PR, degstop)
    if degstop > 0:
        for k in range(degstop):
            hs[k] = xs[0] ** k
        for j in range(1, n):
            hs_prev = hs
            hs[0] = PR.one()
            for k in range(1, degstop):
                hs[k] = hs_prev[k] + xs[j] * hs[k - 1]
    return hs


def generalized_confluent_vandermonde_matrix(la, ys, ka):
    n = len(ka)
    N = sum(ka)
    la_ext = la + [0] * (N - len(la))  
    MyRing = parent(ys[0])
    A = matrix(MyRing, N, N)
    k = 0
    for p in range(n):
        for r in range(ka[p]):
            for j in range(N):
                mypower = la_ext[j] + N - j - r - 1
                coef = binomial(la_ext[j] + N - j - 1, r)
                A[j, k] = coef * (ys[p] ** mypower) if mypower >= 0 else MyRing(0)
            k += 1
    return A


def confluent_vandermonde_det_formula(ys, ka):
    n = len(ka)
    N = sum(ka)
    MyRing = parent(ys[0])
    result = MyRing(1)
    for j in range(n):
        for k in range(j + 1, n):
            result *= (ys[k] - ys[j]) ** (ka[j] * ka[k])
    s = (-1) ** (N * (N - 1) / 2)
    return s * result


def list_with_reps(ys, ka):
    result = [0] * sum(ka)
    k = 0
    for p in range(len(ys)):
        for r in range(ka[p]):
            result[k] = ys[p]
            k += 1
    return result   


def test_sign_change_generalized_confluent_vandermonde(la, ka, r, s, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    ys_changed = list(ys[ : ])
    t = ys_changed[r]
    ys_changed[r] = ys_changed[s]
    ys_changed[s] = t
    ka_changed = list(ka[ : ])
    t = ka_changed[r]
    ka_changed[r] = ka_changed[s]
    ka_changed[s] = t
    lhs = my_det(generalized_confluent_vandermonde_matrix(la, ys_changed, ka_changed))
    column_switches = ka[r] * ka[s] + (ka[r] + ka[s]) * sum(ka[r + 1 : s])
    sign_change = (-1) ** column_switches
    rhs = sign_change * my_det(generalized_confluent_vandermonde_matrix(la, ys, ka))
    if verbose:
        print('test_sign_change_generalized_confluent_vandermonde')
        print('la =', la, ', ka =', ka, ', r =', r, ', s =', s)
        print('lhs =', lhs)
        print('rhs =', rhs)
    return lhs == rhs


def big_symbolic_test_sign_change_generalized_confluent_vandermonde(lambda_sum_max, kappa_sum_max):
    print('big_symbolic_test_sign_change_generalized_confluent_vandermonde,')
    print('lambda_sum_max = %d, kappa_sum_max = %d.' % (lambda_sum_max, kappa_sum_max))
    t0 = time.time()
    nmax = kappa_sum_max
    tests = []
    for n in range(1, nmax):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        for ka in kappa_list:
            N = sum(ka)
            lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
            rs_pairs = [(r, s) for r in range(0, n - 1) for s in range(r + 1, n)]
            tests += [(la, ka, r, s) for la in lambda_list for (r, s) in rs_pairs]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, ka, r, s in tests:
        result = test_sign_change_generalized_confluent_vandermonde(la, ka, r, s, False)
        big_result = big_result and result
        data_str = 'la = ' + str(la) + ', '
        data_str += 'ka = ' + str(ka) + ', '
        data_str += 'r = ' + str(r) + ', '
        data_str += 's = ' + str(s) + ', '
        data_str += str(result)
        print(data_str)
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


#print(big_symbolic_test_sign_change_generalized_confluent_vandermonde(5, 5))

# the following test takes almost one hour on a personal computer with 3.60GHz CPU.
print(big_symbolic_test_sign_change_generalized_confluent_vandermonde(8, 8))

