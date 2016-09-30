import copy
import itertools
import random
def genPartitions(n):
    '''Generates all ordered partitions of n.'''
    if n == 0:
        return [[]]
    return [[k]+L for k in range(1,n+1) for L in genPartitions(n-k)]
def decPartitions(n):
    '''Generates all decreasing partitions of n.'''
    return set([tuple(sorted(x,reverse=True)) for x in genPartitions(n)])
def getIsomorphism(G1, G2, sigma=[]):
    n = len(sigma)
    for i in range(n-1):
        if G1.adjMat[n-1][i] != G2.adjMat[sigma[n-1]][sigma[i]]:
            return None
    if n == G1.n:
        return sigma
    S = set(sigma)
    for i in range(G1.n):
        if i not in S:
            x = getIsomorphism(G1, G2, sigma+[i])
            if x != None:
                return x
    return None
def factorial(n):
    x = 1
    for i in range(1,n+1):
        x *= i
    return x
def CSFMatch(G1, G2):
    a = G1.findCSF()
    b = G2.findCSF()
    if len(a) != len(b):
        return False
    for i in range(len(a)):
        if a[i] != b[i]:
            return False
    return True
class Graph:
    def __init__(self, adjMat):
        if adjMat[0][0] == 0:
            self.adjMat = copy.deepcopy(adjMat)
            self.n = len(self.adjMat)
            for i in range(self.n):
                self.adjMat[i][i] = False
        else:
            self.n = len(adjMat)
            self.adjMat = []
            for i in range(self.n):
                self.adjMat.append([])
                for j in range(self.n):
                    self.adjMat[i].append(False)
            for i in range(self.n):
                for x in adjMat[i]:
                    self.adjMat[i][x] = True
                    self.adjMat[x][i] = True
        self.degrees = []
        for i in range(self.n):
            self.degrees.append(sum(self.adjMat[i]))   
    def isIsomorphic(self, other):
        if set(self.degrees) != set(other.degrees):
            return False
        return getIsomorphism(self, other) != None
    def getHashVal(self):
        '''This is a function of the set of degrees - it will give
           the same value for two isomorphic graphs but could also (but
           probably won't) give the same value for two non-isomorphic graphs.
           This makes testing faster since we only have to test graphs with the same
           hash.'''
        L = sorted(self.degrees)
        k = 1
        ans = 0
        for i in range(self.n):
            k *= 4096
            k %= 1000000007
            ans += k*L[i]
            ans %= 1000000007
        return ans
    def __str__(self):
        s = 'undirected graph on %s vertices:\n' % (self.n)
        s += 'adjacency lists:\n'
        for i in range(self.n):
            L = []
            for j in range(self.n):
                if self.adjMat[i][j]:
                    L.append(j)
            s += '%s: %s\n' % (i,L)
        return s
    def testColoring(self, coloring):
        for i in range(self.n):
            for j in range(i+1,self.n):
                if self.adjMat[i][j] and coloring[i] == coloring[j]:
                    return False
        return True
    def findCSF(self):
        F = []
        L = []
        P = sorted(list(decPartitions(self.n)))
        for L in P:
            coeff = 0
            M = []
            for i in range(len(L)):
                M += [i]*L[i]
            S = set()
            for x in itertools.permutations(M):
                S.add(x)
            for x in S:
                if self.testColoring(x):
                    coeff += 1
            if coeff > 0:
                F.append([L, coeff])
        return F
    def printCSF(self):
        F = self.findCSF()
        print('X_G = ',end='')
        print('%sM_%s' % (('' if F[0][1] == 1 else F[0][1]),F[0][0]),end='')
        for L, c in F[1:]:
            print(' + %sM_%s' % (('' if c == 1 else c),L),end='')
        print()
    def printCSFTex(self):
        F = self.findCSF()
        print('$$X_G = ',end='')
        print('%sm_{%s}' % (('' if F[0][1] == 1 else F[0][1]),str(F[0][0])[1:-1]),end='')
        for L, c in F[1:]:
            print(' + %sm_{%s}' % (('' if c == 1 else c),str(L)[1:-1]),end='')
        print('$$')
    def writeAdjMat(self, fileHandle):
        s = ''
        for i in range(self.n):
            for j in range(self.n):
                if self.adjMat[i][j]:
                    s += '1'
                else:
                    s += '0'
        s += '\n'
        fileHandle.write(s)
    def adjLists(self):
        D = {}
        for i in range(self.n):
            L = []
            for j in range(self.n):
                if self.adjMat[i][j]:
                    L.append(j)
            D[i] = L
        return D
    def printAsyCode(self):
        print('[asy]')
        print('for (int i=0; i<%s; ++i)' % (self.n))
        print('    dot(dir(360.0*i/%s));' % (self.n))
        for i in range(self.n):
            for j in range(i+1,self.n):
                if self.adjMat[i][j]:
                    print('draw(dir(360.0*%s/%s)--dir(360.0*%s/%s));' % (i,self.n,j,self.n))
        print('[/asy]')
    def K3count(self):
        count = 0
        for u in range(self.n-2):
            for v in range(u+1,self.n-1):
                if not self.adjMat[u][v]:
                    continue
                for w in range(v+1,self.n):
                    if self.adjMat[v][w] and self.adjMat[u][w]:
                        count += 1
        return count
def generateGraphs(n, debug=False, verbose=False):
    M = []
    for i in range(n):
        M.append([])
        for j in range(n):
            M[i].append(0)
    isoClasses = []
    isoCounts = []
    hashMap = {}
    Q = []
    for i in range(n):
        for j in range(i+1,n):
            Q.append((i,j))
    for k in range(2**(n*(n-1)//2)):
        if verbose and k%1000 == 0:
            print(k)
        for i in range(n*(n-1)//2):
            M[Q[i][0]][Q[i][1]] = M[Q[i][1]][Q[i][0]] = ((k & (1<<i)) > 0)
        G = Graph(M)
        if debug:
            print('Testing graph')
            print(G)
        h = G.getHashVal()
        if h in hashMap:
            different = True
            for i in hashMap[h]:
                if G.isIsomorphic(isoClasses[i]):
                    if debug:
                        print('Isomorphic to')
                        print(isoClasses[i])
                    isoCounts[i] += 1
                    different = False
                    break
            if different:
                if debug:
                    print('New')
                hashMap[h].append(len(isoClasses))
                isoClasses.append(G)
                isoCounts.append(1)
        else:
            if debug:
                print('New')
            hashMap[h] = [len(isoClasses)]
            isoClasses.append(G)
            isoCounts.append(1)
    return isoClasses, isoCounts
def getRandomGraph(n, edgeProb):
    L = [[0]*n]*n
    for i in range(n):
        for j in range(i+1,n):
            if random.random() < edgeProb:
                L[i][j] = 1
                L[j][i] = 1
    return Graph(L)
def archiveGraphs(n):
    graphs = generateGraphs(n, verbose=True)[0]
    f = open('graphs%s.txt' % (n), 'w')
    for G in graphs:
        G.writeAdjMat(f)
    f.close()
def getGraphs(n):
    f = open('graphs%s.txt' % (n), 'r')
    graphs = []
    for line in f:
        M = []
        for i in range(n):
            M.append([])
            for j in range(n):
                M[i].append(line[n*i+j] == '1')
        graphs.append(Graph(M))
    f.close()
    return graphs
def archiveCSFs(n):
    try:
        graphs = getGraphs(n)
    except:
        archiveGraphs(n)
        graphs = getGraphs(n)
    f = open('CSFs%s.txt' % (n), 'w')
    for G in graphs:
        f.write('%s\n' % (G.findCSF()))
    f.close()
def archiveMatches(n):
    try:
        f = open('CSFs%s.txt' % (n), 'r')
    except:
        archiveCSFs(n)
        f = open('CSFs%s.txt' % (n), 'r')
    L = f.readlines()
    f.close()
    f2 = open('matches%s.txt' % (n), 'w')
    for i in range(len(L)):
        for j in range(i+1, len(L)):
            if L[i] == L[j]:
                f2.write('%s %s\n' % (i,j))
    f2.close()
matchDict = {}
graphs = {}
def processMatches(n,verbose=True):
    global matchDict,graphs
    f = open('matches%s.txt' % (n), 'r')
    L = f.readlines()
    graphs = getGraphs(n)
    part = list(range(len(graphs)))
    #print(part)
    for line in L:
        #print(line)
        s = line.split()
        part[int(s[1])] = part[int(s[0])]
    matchDict = {}
    for x in range(len(part)):
        if part[x] in matchDict:
            matchDict[part[x]].append(x)
        else:
            matchDict[part[x]] = [x]
    counts = [0]*(len(part)+1)
    for x in matchDict:
        counts[len(matchDict[x])] += 1
    if verbose:
        for i in range(1,len(part)+1):
            if counts[i] > 0:
                print('%s: %s' % (i,counts[i]))
        print(len(set(part)))
    f.close()
def CSFMatchLists(n):
    processMatches(n, verbose=False)
    ans = []
    for x in matchDict:
        if len(matchDict[x]) > 1:
            ans.append([copy.deepcopy(graphs[n]) for n in matchDict[x]])
    return ans
def checkDegSets():
    for x in matchDict:
        if len(matchDict[x]) > 1:
            for i in matchDict[x][1:]:
                if set(graphs[i].degrees) != set(graphs[0].degrees):
                    print('different degree sets')
def generateAsy(n, k=-1):
    processMatches(n)
    print('Sets of graphs on %s vertices with equal CSFs:' % (n))
    for x in matchDict:
        if len(matchDict[x]) > 1:
            print('\\newpage')
            graphs[matchDict[x][0]].printCSFTex()
            for i in matchDict[x]:
                graphs[i].printAsyCode()
            k -= 1
            print()
            print()
            if not k:
                return
def checkK3CountMatches(n):
    L = CSFMatchLists(n)
    contra = False
    for S in L:
        k = S[0].K3count()
        for G in S:
            if G.K3count() != k:
                print('counterexample')
                contra = True
    if not contra:
        print('K3 count invariance holds for n = %s' % (n))
def printGraphData(n):
    print('graphs%s = []' % (n))
    for G in getGraphs(n):
        print('graphs%s.append(Graph(%s))' % (n,G.adjLists()))
