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


def jacobi_trudi_matrix_extended(la, xs):
    N = len(xs)
    la_max = la[0] if len(la) > 0 else 0
    la_ext = la + [0] * (N - len(la))
    PR = parent(xs[0])
    hs = hom_polynomials(xs, la_max + N)
    hfun = lambda j: hs[j] if j >= 0 else PR.zero()
    A = matrix(PR, N, N)
    for j in range(N):
        for k in range(N):
            A[j, k] = hfun(la_ext[j] - j + k)
    return A


def elem_polynomials(xs):
    n = len(xs)
    PR = parent(xs[0]) if n > 0 else QQ
    es = vector(PR, n + 1)
    es[0] = PR(1)
    for j in range(n):
        es[j + 1] = es[j] * xs[j]
        for k in range(j, 0, -1):
            es[k] = es[k] + es[k - 1] * xs[j]
    return es


def list_with_reps(ys, ka):
    result = [0] * sum(ka)
    k = 0
    for p in range(len(ys)):
        for r in range(ka[p]):
            result[k] = ys[p]
            k += 1
    return result   


def M_matrix(ys, ka):
    n = len(ka)
    N = sum(ka)
    MyRing = parent(ys[0])
    M = matrix(MyRing, N, N)
    k = 0
    for p in range(n):
        for r in range(ka[p]):
            ka1 = list(ka[ : ])
            ka1[p] -= r + 1
            zs = list_with_reps(ys, ka1)
            es = elem_polynomials(zs)
            for j in range(N):
                mydeg = N - j - r - 1
                mysign = (-1) ** mydeg
                isgood = (mydeg >= 0) and (mydeg <= N - r - 1)
                if isgood:
                    M[j, k] = mysign * es[mydeg]
            k += 1
    return M


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
                mypower = N + la_ext[j] - j - r - 1
                coef = binomial(N + la_ext[j] - j - 1, r)
                A[j, k] = coef * (ys[p] ** mypower) if mypower >= 0 else MyRing(0)
            k += 1
    return A


# tests


def test_G_eq_JM(la, ka, verbose):
    n = len(ka)
    ys = pol_vars('y', n)
    G = generalized_confluent_vandermonde_matrix(la, ys, ka)
    xs = list_with_reps(ys, ka)
    J = jacobi_trudi_matrix_extended(la, xs)
    M = M_matrix(ys, ka)
    JM = J * M
    result = (G == JM)
    if verbose:
        print('test_G_eq_JM')
        print('la =', la)
        print('ka =', ka)
        print('ys =', ys)   
        print('G =')
        print(G)
        print('J = ')
        print(J)
        print('M = ')
        print(M)
        print('JM =')
        print(JM)
        print('result =', result)
    return result


def big_symbolic_test_G_eq_JM(lambda_sum_max, kappa_sum_max):
    print('big_symbolic_test_G_eq_JM,')
    print('lambda_sum_max = %d, kappa_sum_max = %d.' % (lambda_sum_max, kappa_sum_max))
    t0 = time.time()
    nmax = kappa_sum_max
    tests = []
    for n in range(1, nmax):
        kappa_list = partitions_with_given_length_and_bounded_sum(n, kappa_sum_max)
        for ka in kappa_list:
            N = sum(ka)
            lambda_list = partitions_with_bounded_length_and_bounded_sum(N, lambda_sum_max)
            tests += [(la, ka) for la in lambda_list]
    print('number of tests: ' + str(len(tests)))
    big_result = True
    for la, ka in tests:
        result = test_G_eq_JM(la, ka, False)
        big_result = big_result and result
        print('la = ' + str(la) + ', ka = ' + str(ka) + ', ' + str(result))
    print('number of tests: ' + str(len(tests)))
    print('big_result = ' + str(big_result))
    t1 = time.time()
    print('time = %.3g seconds' % (t1 - t0))
    return big_result


print(big_symbolic_test_G_eq_JM(8, 8))

