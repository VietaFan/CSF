# sage code for splitting a set of graphs into disjoint subsets based on the nonzero coefficients in a specified basis
#assumes keeler csf function is defined
def basisCategorize(graphSet,kind='m'):
    csfBases = []
    for G in graphSet:
        csfBases.append(set(p[0] for p in csf(G,kind)))
    n = len(graphSet)
    categories = list(range(n))
    for i in range(n-1):
        for j in range(i+1,n):
            if csfBases[j] == csfBases[i]:
                categories[j] = categories[i]
    D = {}
    for k in range(n):
        if categories[k] not in D:
            D[categories[k]] = [k]
        else:
            D[categories[k]].append(k)
    L = []
    for key in D:
        L.append([])
        for i in D[key]:
            L[-1].append(graphSet[i])
    return L
