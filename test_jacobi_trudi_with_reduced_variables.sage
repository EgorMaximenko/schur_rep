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


def jacobi_trudi_matrix(la, xs):
    la_len = len(la)
    la_max = la[0] if len(la) > 0 else 0
    PR = parent(xs[0])
    hs = hom_polynomials(xs, la_max + la_len)
    hfun = lambda j: hs[j] if j >= 0 else PR.zero()
    A = matrix(PR, la_len, la_len)
    for j in range(la_len):
        for k in range(la_len):
            A[j, k] = hfun(la[j] - j + k)
    return A


def jacobi_trudi_matrix_extended_with_reduced_variables(la, xs):
    N = len(xs)
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    PR = parent(xs[0])
    A = matrix(PR, N, N)
    for k in range(N):
        hs = hom_polynomials(xs[k : N], la_max + N)
        hfun = lambda j: hs[j] if j >= 0 else PR.zero()
        for j in range(N):
            A[j, k] = hfun(la_ext[j] - j + k)
    return A


# tests


def test_schur_via_jacobi_trudi_with_reduced_variables(la, N, verbose):
    xs = pol_vars('x', N)
    A0 = jacobi_trudi_matrix(la, xs)
    r0 = my_det(A0)
    A1 = jacobi_trudi_matrix_extended_with_reduced_variables(la, xs)
    r1 = my_det(A1)
    if verbose:
        print('test_schur_via_jacobi_trudi_with_reduced_variables')
        print('la = ' + str(la) + ', N = ' + str(N))
        print(r0)
        print(r1)
    return r0 == r1


def big_symbolic_test_schur_via_jacobi_trudi_with_reduced_variables(lambda_sum_max, N_max):
    print('big_symbolic_test_schur_via_jacobi_trudi_with_reduced_variables,')
    print('lambda_sum_max = %d, N_max = %d.' % (lambda_sum_max, N_max))
    t0 = time.time()
    tests = []
    for N in range(1, N_max):
        lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
        tests += [(la, N) for la in lambda_list]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, N in tests:
        result = test_schur_via_jacobi_trudi_with_reduced_variables(la, N, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', N = ' + str(N) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


print(big_symbolic_test_schur_via_jacobi_trudi_with_reduced_variables(16, 8))

