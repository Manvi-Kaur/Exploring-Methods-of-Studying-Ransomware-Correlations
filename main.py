from ast import Lambda
#from audioop import reverse
from cProfile import label
from ctypes import util
from email import header
from itertools import count
from platform import node
#import this
import pandas as pd 
import domain, utils
import tabulate as tb
from typing import Counter, List
import matplotlib.pyplot as plt 
import seaborn as sns
import numpy as np
import networkx as nx 
import domain, utils
import statistics, math
import igraph
from networkx.algorithms import bipartite as bp
from networkx.algorithms import community as nxcm
import scipy.stats as stats
from sklearn.metrics.pairwise import cosine_similarity
from scipy import spatial
# from apyori import apriori
from mlxtend.preprocessing import TransactionEncoder
from mlxtend.frequent_patterns import apriori, fpmax, fpgrowth
from mlxtend.frequent_patterns import association_rules
from prefixspan import PrefixSpan
import functools
from scipy.stats import pointbiserialr


tactics : List['domain.Tactic'] = []
techniques : List['domain.Technique'] = []
procedures  : List['domain.Procedure'] = []
groups  : List['domain.Group'] = []
softwares  : List['domain.Software'] = []
cocTTPs : List[List['domain.Technique']] = []

utils.buildDataSchema(tactics, techniques, procedures, groups, softwares)
cocGraph : nx.Graph = utils.initializeCocGraph(groups, softwares, cocTTPs, techniques, tactics)
cocDiGraph : nx.DiGraph =  utils.generateDiGraph2(cocTTPs, techniques, tactics)

def mitigation_coverage(mitigations, techniques):
    coverage_results = {}
    
    for technique in techniques:
        coverage_results[technique.id] = []
        
        for mitigation in mitigations:
            if technique in mitigation.techniques:
                coverage_results[technique.id].append(mitigation.name)
    
    print(coverage_results)
    return coverage_results

# *** find top occurring techniques (Table III)
'''def findTopTenTechniques(techniques, cocTTPs):
    techniquesSortedBySupport = []
    for te in techniques:
        sum = 0
        for coc in cocTTPs:
            if te in coc: 
                sum += 1
        techniquesSortedBySupport.append((te, sum))

    techniquesSortedBySupport.sort(key = lambda v : v[1], reverse=True)

    idx = 0
    for item in techniquesSortedBySupport[0:10]:
        idx += 1
        print(f"[{idx}] {item[0].id}: {item[0].name} @ {item[0].tactics[0].id}: {item[0].tactics[0].name} ==> {item[1]/len(cocTTPs)}")
    return techniquesSortedBySupport'''
def findTopTenTechniques(techniques, cocTTPs):
    techniquesSortedBySupport = []
    for te in techniques:
        support_sum = 0  # Renaming the variable to avoid conflict with built-in function 'sum'
        for coc in cocTTPs:
            if te in coc: 
                support_sum += 1
        techniquesSortedBySupport.append((te, support_sum))

    techniquesSortedBySupport.sort(key = lambda v : v[1], reverse=True)

    idx = 0
    for item in techniquesSortedBySupport[0:10]:
        idx += 1
        print(f"[{idx}] {item[0].id}: {item[0].name} @ {item[0].tactics[0].id}: {item[0].tactics[0].name} ==> {item[1]/len(cocTTPs)}")
    
    # Anomaly detection based on deviation from average support
    threshold = 0.1  # Example threshold for anomaly detection
    avg_support = sum([s for te, s in techniquesSortedBySupport]) / len(techniquesSortedBySupport)
    anomalies = [(te, support) for te, support in techniquesSortedBySupport if support < avg_support * threshold]

    # Print detected anomalies
    print("\nDetected anomalies:")
    for te, support in anomalies:
        print(f"{te.id}: {te.name} - Support: {support}")

    return


# *** find top tactics (Table IV)
def findTopTactics(techniques, tactics, cocTTPs):
    techniquesSortedBySupport = []
    for te in techniques:
        sum = 0
        for coc in cocTTPs:
            if te in coc: 
                sum += 1
        techniquesSortedBySupport.append((te, sum))

    techniquesSortedBySupport.sort(key = lambda v : v[1], reverse=True)

    idx = 0
    for item in techniquesSortedBySupport[0:10]:
        idx += 1
        print(f"[{idx}] {item[0].id}: {item[0].name} @ {item[0].tactics[0].id}: {item[0].tactics[0].name} ==> {item[1]/len(cocTTPs)}")
    
    
    topFourteenTechniques = []
    topTechniquesWithMinSpprt = [x[0] for x in techniquesSortedBySupport if x[1] > 59.9]

    columns = ['support', 'count', 'min', 'avg', 'med', 'stdev', 'max', 'top']
    index = [ta.id + ': ' + ta.name for ta in tactics]
    df = pd.DataFrame(index=index, columns=columns)

    for ta in tactics:
        topTechInThisTa = None
        maxValue = -1
        values = []
        support = 0
        for coc in cocTTPs:
            if ta in [x.tactics[0] for x in coc]:
                support += 1
        for te in topTechniquesWithMinSpprt:
            if te.tactics[0] == ta:
                value = [x[1] for x in techniquesSortedBySupport if x[0] == te][0]
                values.append(value/len(cocTTPs))
                if value > maxValue:
                    topTechInThisTa = te
                    maxValue = value
        if len(values) > 0:
            if len(values) > 1:
                topFourteenTechniques.append(topTechInThisTa)
                df.loc[f"{ta.id}: {ta.name}"] = [(support/len(cocTTPs)), (len(values)), (min(values)), (statistics.mean(values)), (statistics.median(values)), (statistics.stdev(values)), (max(values)), (topTechInThisTa.id + ': ' + topTechInThisTa.name)]
            if len(values) == 1:
                topFourteenTechniques.append(topTechInThisTa)
                df.loc[f"{ta.id}: {ta.name}"] = [(support/len(cocTTPs)), (len(values)), (min(values)), (statistics.mean(values)), (statistics.median(values)), (0), (max(values)), (topTechInThisTa.id + ': ' + topTechInThisTa.name)]

    for cols in columns[:-1]:
        df[cols] = df[cols].astype(float)
    df = df.round(2)
    print(tb.tabulate(df.sort_values(by='support', ascending=False), headers='keys', tablefmt='psql'))
    return 

# top ten combinations (Table V)
def getTopTenCombinations(cocTTPs):
    rules = utils.generateRules(cocTTPs)

    rules['alen'] = rules['antecedents'].apply(lambda x : len(x)) 
    rules['clen'] = rules['consequents'].apply(lambda x : len(x)) 
    dfq = rules.query("alen + clen == 2")

    print(dfq[['antecedents', 'consequents', 'support', 'confidence']].sort_values(by='support', ascending=False).head(20))
    return

# get top ten simple rules (Table VI)
def getTopTenSimpleRules(cocTTPs):
    rules = utils.generateRules(cocTTPs)

    rules['alen'] = rules['antecedents'].apply(lambda x : len(x)) 
    rules['clen'] = rules['consequents'].apply(lambda x : len(x)) 
    dfq = rules.query("alen + clen == 2")

    print(dfq[['antecedents', 'consequents', 'support', 'confidence']].sort_values(by='support', ascending=False).head(20))
    return

# get top ten compound rules (Table VII)
def getTopTenCompoundRules(cocTTPs):
    rules = utils.generateRules(cocTTPs)

    rules['alen'] = rules['antecedents'].apply(lambda x : len(x)) 
    rules['clen'] = rules['consequents'].apply(lambda x : len(x)) 
    dfq = rules.query("alen + clen > 2")

    print(dfq[['antecedents', 'consequents', 'support', 'confidence']].sort_values(by='confidence', ascending=False).head(20))
    return

# get the adjacency matrix of the co-occurrence network (table VIII)
def getAdjacencyMatrix(cocDiGraph, techniques):
    print('*** printing the adjacency matrix ***')
    # print(dod)
    nodelists = list(cocDiGraph.nodes())

    Index = nodelists
    Columns = nodelists

    IndexWithTTPsObject = []
    for idx in Index:
        te = next((x for x in techniques if x.id == idx), None)
        IndexWithTTPsObject.append(te)

    IndexWithTTPsObject.sort(key = lambda v : v.id)
    IndexWithTTPsObject.sort(key = lambda v : v.tactics[0].sequence)
    Index = [f'{x.id}' for x in IndexWithTTPsObject]
    Columns = [f'{x.id}' for x in IndexWithTTPsObject]

    # for item in IndexWithTTPsObject:
    #     print(f'{item.id}: {item.name} | {item.tactics[0].id}: {item.tactics[0].name}')
    # Create an empty adjacency matrix
    adjacency_matrix = []

    for ix in Index:
        row = []
        for cl in Columns:
            if cocDiGraph.has_edge(ix, cl):
                row.append(1)  # If there's an edge between ix and cl, mark it as 1
            else:
                row.append(0)  # Otherwise, mark it as 0
        adjacency_matrix.append(row)

    # Convert the adjacency matrix to a numpy array for plotting
    adjacency_matrix = np.array(adjacency_matrix)

    df = pd.DataFrame(index=Index, columns=Columns)

    for ix in Index:
        for cl in Columns:
            if cocDiGraph.has_edge(ix, cl):
                df.at[ix, cl] = '*'
            else:
                df.at[ix, cl] = ' '
    df.to_csv('file1.csv')
    print(tb.tabulate(df, headers='keys', showindex=True, tablefmt='psql'))

def getAdjacencyMatrix1(cocDiGraph, techniques):
    print('*** printing the adjacency matrix ***')

    nodelists = list(cocDiGraph.nodes())

    Index = nodelists
    Columns = nodelists

    IndexWithTTPsObject = []
    for idx in Index:
        te = next((x for x in techniques if x.id == idx), None)
        IndexWithTTPsObject.append(te)

    IndexWithTTPsObject.sort(key=lambda v: v.id)
    IndexWithTTPsObject.sort(key=lambda v: v.tactics[0].sequence)
    Index = [f'{x.id}' for x in IndexWithTTPsObject]
    Columns = [f'{x.id}' for x in IndexWithTTPsObject]

    # Create an empty adjacency matrix
    '''
    adjacency_matrix = []

    for ix in Index:
        row = []
        for cl in Columns:
            if cocDiGraph.has_edge(ix, cl):
                edge_count = cocDiGraph[ix][cl]['weight'] if 'weight' in cocDiGraph[ix][cl] else 0
                row.append(edge_count)  # Fill count of edge occurrences
            else:
                row.append(0)  # No edge, fill with 0
        adjacency_matrix.append(row)

    # Convert the adjacency matrix to a numpy array (optional for some libraries)
    adjacency_matrix = np.array(adjacency_matrix)'''

    # Create a pandas dataframe for easy manipulation
    df = pd.DataFrame(index=Index, columns=Columns)
    
    # Assume 'df' is your Pandas DataFrame initialized to store the adjacency matrix
    for ix in cocDiGraph.nodes():
        for cl in cocDiGraph.nodes():
            if cocDiGraph.has_edge(ix, cl):
                # Retrieve the count attribute for the edge
                edge_count = cocDiGraph[ix][cl]['count'] if 'count' in cocDiGraph[ix][cl] else 0
                df.at[ix, cl] = edge_count  # Fill with the count of transactions supporting the rule
            else:
                df.at[ix, cl] = 0  # No edge, fill with 0

    all_counts = [cocDiGraph[edge[0]][edge[1]]['count'] for edge in cocDiGraph.edges()]
    normalized_counts = utils.normalizeList(all_counts)
    count_to_normalized = {original: normalized for original, normalized in zip(all_counts, normalized_counts)}
    for ix in cocDiGraph.nodes():
        for cl in cocDiGraph.nodes():
            if cocDiGraph.has_edge(ix, cl):
                # Retrieve the original count
                original_count = cocDiGraph[ix][cl]['count']
                # Get the normalized value from the mapping
                normalized_value = count_to_normalized.get(original_count, 0)
                df.at[ix, cl] = normalized_value



    # Save the dataframe as a CSV file
    df.to_csv('adjacency_matrix1.csv', index=True, header=True)

    print(df.to_string())

import numpy as np
import pandas as pd

def getAdjacencyMatrix2(cocDiGraph, techniques):
    print('*** printing the adjacency matrix ***')

    nodelists = list(cocDiGraph.nodes())

    Index = nodelists
    Columns = nodelists

    IndexWithTTPsObject = []
    for idx in Index:
        te = next((x for x in techniques if x.id == idx), None)
        IndexWithTTPsObject.append(te)

    IndexWithTTPsObject.sort(key=lambda v: v.id)
    IndexWithTTPsObject.sort(key=lambda v: v.tactics[0].sequence)
    Index = [f'{x.id}' for x in IndexWithTTPsObject]
    Columns = [f'{x.id}' for x in IndexWithTTPsObject]

    # Create an empty adjacency matrix
    adjacency_matrix = []

    for ix in Index:
        row = []
        for cl in Columns:
            if cocDiGraph.has_edge(ix, cl):
                edge_count = cocDiGraph[ix][cl]['weight'] if 'weight' in cocDiGraph[ix][cl] else 0
                row.append(edge_count)  # Fill count of edge occurrences
            else:
                row.append(0)  # No edge, fill with 0
        adjacency_matrix.append(row)

    # Convert the adjacency matrix to a numpy array (optional for some libraries)
    adjacency_matrix = np.array(adjacency_matrix)

    # Create a pandas dataframe for easy manipulation
    df = pd.DataFrame(index=Index, columns=Columns)

    for ix in Index:
        for cl in Columns:
            if cocDiGraph.has_edge(ix, cl):
                edge_count = cocDiGraph[ix][cl]['weight'] if 'weight' in cocDiGraph[ix][cl] else 0
                df.at[ix, cl] = edge_count  # Fill count of edge occurrences
            else:
                df.at[ix, cl] = 0  # No edge, fill with 0

    # Save the dataframe as a CSV file
    df.to_csv('adjacency_matrix_confidence.csv', index=True, header=True)

    print(df.to_string())


# get technique centrality measures (table IX)
'''def getTechniqueCentrality(cocDiGraph : nx.DiGraph, techniques : List['domain.Technique'], tactics : List['domain.Tactic']):
    
    dcofNodes = nx.degree_centrality(cocDiGraph)
    bcOfNodes = nx.betweenness_centrality(cocDiGraph, normalized = False)
    
    # pcInOfNodes = nx.katz_centrality(cocDiGraph, normalized = True)
    # pcOutOfNodes = nx.katz_centrality(cocDiGraph.reverse(), normalized = True)
    
    # ccInOfNodes = nx.closeness_centrality(cocDiGraph, wf_improved=True)
    # ccOutOfNodes = nx.closeness_centrality(cocDiGraph.reverse(), wf_improved=True)
    
    techniqueIds = []
    techniqueNames = []
    dcinvalues = []
    dcoutvalues = []
    # ccinvalues = []
    # ccoutvalues = []
    bcvalues = []
    # pcinvalues = []
    # pcoutvalues = []
    tacticsList = []
    
    techniuqesInGraph = [x for x in techniques if x.id in list(cocDiGraph.nodes())]
    
    for te in techniuqesInGraph:
        techniqueIds.append(te.id)
        techniqueNames.append(te.name)
        
        dcinvalues.append((cocDiGraph.in_degree[te.id]))
        dcoutvalues.append((cocDiGraph.out_degree[te.id]))
        # ccinvalues.append(ccInOfNodes[te.id])
        # ccoutvalues.append(ccOutOfNodes[te.id])
        bcvalues.append(bcOfNodes[te.id])
        # pcinvalues.append(pcInOfNodes[te.id])
        # pcoutvalues.append(pcOutOfNodes[te.id])
        
        # ta = next((x for x in tactics if x in te.tactics), None)
        # tacticsList.append(ta.id)
        
        ta = cocDiGraph.nodes[te.id]['tactic']
        tacticsList.append([x.name for x in tactics if x.id == ta][0])
        
    x=0
    data = {
        'id' : techniqueIds, 
        'Technique': techniqueNames, 
        'Tactic': tacticsList, 
        'IDC': dcinvalues,
        'ODC': dcoutvalues,  
        # 'bc': utils.normalizeList(bcvalues), 
        # 'cci': utils.normalizeList(ccinvalues),
        # 'cco': utils.normalizeList(ccoutvalues),
        # 'pci': utils.normalizeList(pcinvalues),
        # 'pco': utils.normalizeList(pcoutvalues)
        'BC': bcvalues, 
        # 'ICC': ccinvalues,
        # 'OCC': ccoutvalues,
        # 'IKC': pcinvalues,
        # 'OKC': pcoutvalues
    }
    
    df = pd.DataFrame(data)
    df = df.round(2)
    
    tacticnames = df['Tactic'].tolist()
    print(f"dci: {min(dcinvalues)} {statistics.mean(dcinvalues)} {statistics.quantiles(dcinvalues, n=4)}")
    print(f"dco: {min(dcoutvalues)} {statistics.mean(dcoutvalues)} {statistics.quantiles(dcoutvalues, n=4)}")
    print(f"bc: {min(bcvalues)} {statistics.mean(bcvalues)} {statistics.quantiles(bcvalues, n=4)}")
    # print(f"cci: {min(ccinvalues)} {statistics.mean(ccinvalues)} {statistics.quantiles(ccinvalues, n=4)}")
    # print(f"cco: {min(ccoutvalues)} {statistics.mean(ccoutvalues)} {statistics.quantiles(ccoutvalues, n=4)}")
    # print(f"kci: {min(pcinvalues)} {statistics.mean(pcinvalues)} {statistics.quantiles(pcinvalues, n=4)}")
    # print(f"kco: {min(pcoutvalues)} {statistics.mean(pcoutvalues)} {statistics.quantiles(pcoutvalues, n=4)}")
    
    print(f'*** centrality of techniques ***')
    print(tb.tabulate(df.sort_values(by=['IDC'], ascending=False).head(60), headers='keys', showindex=False, tablefmt='psql'))
    print(f'*** centrality of techniques stat ***')
    # print(tb.tabulate(df.describe(), headers='keys', tablefmt='psql'))
    
    # cclist = df['pc'].tolist()
    # print(np.percentile(cclist, 75))
    
    # print(tb.tabulate(df.corr().round(2),headers='keys', showindex=True, tablefmt='latex'))
    
    # dfm = pd.melt(df, id_vars=['id'], value_vars=['dc', 'cc', 'bc', 'pc'])
    # sns.violinplot(data=dfm, x='variable', y='value', inner='quartile',)
    #plt.show()
    
    
    dfq = df.query('Tactic == "TA0011"')
    # print(df.describe())
    
    ranges = []
    nodeCounts = []
    hueList = []
    
    bcvalues = utils.normalizeList(bcvalues)
    # ccinvalues = utils.normalizeList(ccinvalues)
    # pcinvalues = utils.normalizeList(pcinvalues)
    # ccoutvalues = utils.normalizeList(ccoutvalues)
    # pcoutvalues = utils.normalizeList(pcoutvalues)
    
    for i in range(0, 100, 20):
        nodeCount = len([x for x in bcvalues if x >= i/100 and x < (i+20)/100])
        ranges.append(f'{i/100}-{(i+20)/100}')
        hueList.append('BC')
        nodeCounts.append(nodeCount)
    return'''

def getTechniqueCentrality(cocDiGraph: nx.DiGraph, techniques: List['domain.Technique']):
        """
        Calculates various centrality measures for techniques in the co-occurrence network

        Args:
            cocDiGraph: Directed co-occurrence network graph
            techniques: List of Technique objects

        Returns:
            A Pandas DataFrame containing centrality measures for each technique
        """
        
        dcofNodes = nx.degree_centrality(cocDiGraph)
        bcOfNodes = nx.betweenness_centrality(cocDiGraph, normalized=False)
        # Eigenvector centrality
        evcOfNodes = nx.eigenvector_centrality(cocDiGraph)
        
        # Try different alpha values for Katz centrality
        alpha_values = [0.1, 0.2, 0.3, 0.4, 0.5]  # Adjust as needed
        katzOfNodes = {}
        for alpha in alpha_values:
            try:
                katzOfNodes = nx.katz_centrality(cocDiGraph, alpha=alpha, max_iter=2000)
                break  # If successful, exit the loop
            except nx.PowerIterationFailedConvergence:
                continue  # Try the next alpha value
        
        techniqueIds = []
        techniqueNames = []
        dcinvalues = []
        dcoutvalues = []
        evcinvalues = []
        evcoutvalues = []
        bcinvalues = []
        katzinvalues = []
        katzoutvalues = []
        print('reached this point')
        for te in techniques:
            if te.id in cocDiGraph.nodes():
                techniqueIds.append(te.id)
                techniqueNames.append(te.name)
                dcinvalues.append(cocDiGraph.in_degree[te.id])
                dcoutvalues.append(cocDiGraph.out_degree[te.id])
                evcinvalues.append(evcOfNodes[te.id])
                evcoutvalues.append(evcOfNodes[te.id])  # Eigenvector centrality is undirected
                bcinvalues.append(bcOfNodes[te.id])
                katzinvalues.append(katzOfNodes[te.id])
                katzoutvalues.append(katzOfNodes[te.id])  # Katz centrality is undirected

        data = {
            'id': techniqueIds,
            'Technique': techniqueNames,
            'IDC': dcinvalues,
            'ODC': dcoutvalues,
            'EVC': evcinvalues,
            'BC': bcinvalues,
            'Katz': katzinvalues,
        }

        df = pd.DataFrame(data)
        
        # Assuming technique severity data is available in a 'severity' attribute
        if hasattr(techniques[0], 'severity'):
            technique_severities = [t.severity for t in techniques]
            df['Severity'] = technique_severities
            
            # Calculate correlation between centrality measures and severity
            correlation_matrix = df[['IDC', 'ODC', 'EVC', 'BC', 'Katz', 'Severity']].corr(method='spearman')
            print('printing correlation matrix')
            print(correlation_matrix.round(2))
        return df


def findTopMitigationTechniquesBySupport(techniques, tactics, cocTTPs):
    techniquesSortedBySupport = []
    for te in techniques:
        sum = 0
        for coc in cocTTPs:
            if te in coc:
                sum += 1
        techniquesSortedBySupport.append((te, sum))

    techniquesSortedBySupport.sort(key=lambda v: v[1], reverse=True)

    idx = 0
    for item in techniquesSortedBySupport[0:10]:
        idx += 1
        print(
            f"[{idx}] {item[0].id}: {item[0].name} @ {item[0].tactics[0].id}: {item[0].tactics[0].name} ==> {item[1]/len(cocTTPs)}")
    return

#print('cocTTPs: ', cocTTPs)
findTopTenTechniques(techniques, cocTTPs)
findTopTactics(techniques, tactics, cocTTPs)
#print("TopTenCombinations", cocTTPs)
getTopTenCombinations(cocTTPs)
#print("TopTenSimpleRules", cocTTPs)
getTopTenSimpleRules(cocTTPs)
#print("TopTenCompoundRules", cocTTPs)
getTopTenCompoundRules(cocTTPs)
getAdjacencyMatrix(cocDiGraph, techniques)
getTechniqueCentrality(cocDiGraph, techniques)
#findTopMitigationTechniquesBySupport(techniques, tactics, cocTTPs)
#getAdjacencyMatrix2(cocDiGraph, techniques)

