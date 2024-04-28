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

    # Print the total number of simple rules generated
    total_simple_rules = len(dfq)
    print(f"Total number of simple rules generated: {total_simple_rules}")

    print(dfq[['antecedents', 'consequents', 'support', 'confidence']].sort_values(by='support', ascending=False).head(20))
    return

# get top ten compound rules (Table VII)
def getTopTenCompoundRules(cocTTPs):
    rules = utils.generateRules(cocTTPs)

    rules['alen'] = rules['antecedents'].apply(lambda x : len(x)) 
    rules['clen'] = rules['consequents'].apply(lambda x : len(x)) 
    dfq = rules.query("alen + clen > 2")

    # Print the total number of simple rules generated
    total_compound_rules = len(dfq)
    print(f"Total number of compound rules generated: {total_compound_rules}")

    print(dfq[['antecedents', 'consequents', 'support', 'confidence']].sort_values(by='confidence', ascending=False).head(20))
    return


def getAdjacencyMatrix(cocDiGraph, techniques):
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
                df.at[ix, cl] = edge_count 
            else:
                df.at[ix, cl] = 0  

    
    df.to_csv('adjacency_matrix_confidence.csv', index=True, header=True)

    print(df.to_string())


findTopTenTechniques(techniques, cocTTPs)
findTopTactics(techniques, tactics, cocTTPs)
getTopTenCombinations(cocTTPs)
getTopTenSimpleRules(cocTTPs)
getTopTenCompoundRules(cocTTPs)
getAdjacencyMatrix(cocDiGraph, techniques)

