from cmath import nan
import gc
import re, networkx as nx
import pandas as pd
import domain
import tabulate as tb
from typing import Counter, List
#from audioop import reverse
from email import header
from itertools import count
import pandas as pd 
import domain, utils
import tabulate as tb
from typing import List
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
from itertools import count

def find_citation(text : str) -> str:
    tokens = text.split('(Citation: ')
    tokens = tokens[-1].strip().split(' ')
    outputText = ''
    for index in range(0, len(tokens)):
        outputText = outputText + ' ' + tokens[index]
    return outputText[0:-1].strip()

def findYear(text : str) -> str:
    regexPattern = r'''[0-9][0-9][0-9][0-9]'''
    match = re.search(regexPattern, text)
    return text[match.span()[0] : match.span()[1]]

def initializeTactics(tactics : List['domain.Tactic']) -> None:
    dfTactic = pd.read_excel('ttps.xlsx', sheet_name='tactic')
    for row in dfTactic.itertuples():
        tactic = domain.Tactic(row.tacticId, row.tacticName)
        
        if row.tacticId == 'TA0043' : tactic.sequence = 1
        if row.tacticId == 'TA0042' : tactic.sequence = 2
        if row.tacticId == 'TA0001' : tactic.sequence = 3
        if row.tacticId == 'TA0002' : tactic.sequence = 4
        if row.tacticId == 'TA0003' : tactic.sequence = 5
        if row.tacticId == 'TA0004' : tactic.sequence = 6
        if row.tacticId == 'TA0005' : tactic.sequence = 7
        if row.tacticId == 'TA0006' : tactic.sequence = 8
        if row.tacticId == 'TA0007' : tactic.sequence = 9
        if row.tacticId == 'TA0008' : tactic.sequence = 10
        if row.tacticId == 'TA0009' : tactic.sequence = 11
        if row.tacticId == 'TA0011' : tactic.sequence = 12
        if row.tacticId == 'TA0010' : tactic.sequence = 13
        if row.tacticId == 'TA0040' : tactic.sequence = 14
        
        
        tactics.append(tactic)

def initializeTechniques(techniques : List['domain.Technique']) -> None:
    dfTechnique = pd.read_excel('ttps.xlsx', sheet_name='technique')
    for row in dfTechnique.itertuples():
        ifAny = [x for x in techniques if x.id == row.techniqueId]
        if len(ifAny) == 0:
            technique = domain.Technique(row.techniqueId, row.techniqueName)
            techniques.append(technique)

def initializeTacticTechniqueMapping(tactics : List['domain.Tactic'], techniques : List['domain.Technique']) -> None:
    dfTechnique = pd.read_excel('ttps.xlsx', sheet_name='technique')
    for row in dfTechnique.itertuples():
        technique = [x for x in techniques if x.id == row.techniqueId][0]
        tactic = [x for x in tactics if x.id == row.tactics][0]
        if tactic not in technique.tactics: technique.tactics.append(tactic)
        if technique not in tactic.techniques: tactic.techniques.append(technique)

def initializeProcedures(procedures : List['domain.Procedure'], techniques : List['domain.Technique']) -> None:
    dfProcedures = pd.read_excel('technique1.xlsx', sheet_name='procedure')
    print('Techniques file accessed')
    dfProcedures = dfProcedures[['sourceID', 'targetID']]  # Remove the citation column
    dfProcedures['targetID'] = dfProcedures['targetID'].apply(lambda row : row[0:5])

    for row in dfProcedures.itertuples():
        procedure = domain.Procedure(row.sourceID + ':' + row.targetID)
        procedure.technique = next( (x for x in techniques if x.id == row.targetID[:5]), None)
        procedure.name = row.sourceID + ':' + row.targetID
        if 'G' in procedure.id: 
            procedure.type = 'group'
        else: 
            procedure.type = 'software'
        procedures.append(procedure)


def initializeGroups(groups : List['domain.Group'], techniques : List['domain.Technique']) -> None:
    dfGroups = pd.read_excel('groups1.xlsx', sheet_name='ttps')
    #print("Groups file accessed.")
    dfGroups = dfGroups[['sourceID', 'targetID']]
    dfGroups['targetID'] = dfGroups['targetID'].apply(lambda v : v[0:5])
    dfGroups = dfGroups.drop_duplicates()
    dfg = dfGroups.groupby(['sourceID'])
    
    for name, group in dfg:
        g = domain.Group(name)
        
        for row in group.itertuples():
            #print("Row target ID:", row.targetID)
            matching_techniques = [x for x in techniques if x.id == row.targetID]
            #print("Matching Techniques:", matching_techniques)
            if matching_techniques:
                ttp = matching_techniques[0]
                if ttp not in g.techniques: 
                    g.techniques.append(ttp)
            #else:
                #print("No matching technique found for target ID:", row.targetID)
        groups.append(g)



def initializeSoftwares(softwares : List['domain.Software'], techniques : List['domain.Technique']) -> None:
    dfSoftwares = pd.read_excel('software1.xlsx', sheet_name='ttps')
    print('Software File accessed.')
    dfSoftwares = dfSoftwares[['sourceID', 'targetID']]
    dfSoftwares['targetID'] = dfSoftwares['targetID'].apply(lambda v : v[0:5])
    dfSoftwares = dfSoftwares.drop_duplicates()
    dfg = dfSoftwares.groupby(['sourceID'])

    
    for name, group in dfg:
        software = domain.Software(name)
        
        for row in group.itertuples():
            #print("Row target ID:", row.targetID)
            matching_techniques = [x for x in techniques if x.id == row.targetID]
            #print("Matching Techniques:", matching_techniques)
            if matching_techniques:
                ttp = matching_techniques[0]
                if ttp not in software.techniques: 
                    software.techniques.append(ttp)
        softwares.append(software)



def buildDataSchema(tactics: List['domain.Tactic'], techniques: List['domain.Technique'], procedures: List['domain.Procedure'], groups: List['domain.Group'], softwares: List['domain.Software']) -> None:
    initializeTactics(tactics)
    initializeTechniques(techniques)
    initializeTacticTechniqueMapping(tactics, techniques)
    initializeProcedures(procedures, techniques)
    initializeGroups(groups, techniques)
    initializeSoftwares(softwares, techniques)
    return

def degree_centrality(graph):
    max = 0
    for edge in graph.edges:
        if max < graph.edges[edge]['count']:
            max = graph.edges[edge]['count']

    dc = {}
    for node in graph.nodes:
        total = 0
        for item in graph.neighbors(node):
            total += graph.edges[node, item]['count']
        dc[f'{node}'] = total/(max*len(graph))
    return dc

def initializeCocGraph(groupsList : List['domain.Group'], softwareList : List['domain.Software'], cocTTPs : List[List['domain.Technique']], techniques : List['domain.Technique'], tactics : List['domain.Tactic'], min_cooccurring_technique = 3, min_pct_cooccurrence = 5) -> nx.Graph:
    allTechniques = []

    for g in groupsList:
        for te in g.techniques:
            allTechniques.append(te)

    allTechniques = list( set(allTechniques) )

    for s in softwareList:
        for te in s.techniques:
            allTechniques.append(te)

    allTechniques = list( set(allTechniques) )
    allTechniques.sort(key=lambda t : t.id)

    # cocTTPs = []
    cocTTPs.extend([g.techniques for g in groupsList if len(g.techniques) >= min_cooccurring_technique])
    cocTTPs.extend([s.techniques for s in softwareList if len(s.techniques) >= min_cooccurring_technique])

    ttpsTuples = []

    for ttp1 in allTechniques:
        for ttp2 in allTechniques:
            count = 0
            for item in cocTTPs:
                if ttp1 in item and ttp2 in item and ttp1 != ttp2:
                    count += 1
            if (ttp1, ttp2, count) not in ttpsTuples and (ttp2, ttp1, count) not in ttpsTuples and ttp1 != ttp2 and count > len(cocTTPs)*min_pct_cooccurrence/100:
                ttpsTuples.append((ttp1, ttp2, count))

    ttpsTuples.sort(key= lambda i : i[2], reverse=True)
    
    graph = nx.Graph()
    graph.add_nodes_from([x.id for x in allTechniques])
        
    for node in graph.nodes:
        graph.nodes[node]['tactic'] = next( (x.tactics[0].id for x in techniques if x.id == node) )
        te = next( (x for x in techniques if x.id == node) )
        graph.nodes[node]['frequency'] = len([x for x in cocTTPs if te in x])
        # print(graph.nodes[node])

    for item in ttpsTuples:
        graph.add_edge(item[0].id, item[1].id, count = item[2], distance = ttpsTuples[0][2] + 1 - item[2])
    
    return graph

def generateRules(cocTTPs : List[List['domain.Technique']]):
    transactions = []

    for cases in cocTTPs:
        transaction = []
        transaction.extend( [x.id for x in cases] )
        transactions.append(transaction)

    # print(transactions)
    te = TransactionEncoder()
    te_ary = te.fit(transactions).transform(transactions)
    df = pd.DataFrame(te_ary, columns=te.columns_)
    # print(df.head())

    frequent_itemsets = fpgrowth(df, min_support=0.10, use_colnames=True)
    frequent_itemsets['len'] = frequent_itemsets['itemsets'].apply(lambda x : len(x))
    
    dflen = frequent_itemsets.query("len == 2")
    
    ttt = [list(x)[0] for x in dflen['itemsets'].tolist()]
    print(f'=========={len(set(ttt))}')
    
    lengths = []
    for item in frequent_itemsets.itertuples():
        lengths.append(len(item.itemsets))

    rules = association_rules(frequent_itemsets, metric="confidence", min_threshold=0.505)
    print(f'*** rules ***')
    print(len(rules))
    
    rules['alen'] = rules['antecedents'].apply(lambda x : len(x)) 
    rules['clen'] = rules['consequents'].apply(lambda x : len(x)) 

    dfq = rules.query("alen + clen == 2")
    return rules

def generateRulesTactic(cocTTPs : List[List['domain.Technique']]):
    transactions = []

    for cases in cocTTPs:
        transaction = []
        transaction.extend( [x.tactics[0].id for x in cases] )
        transaction = list(set(transaction))
        transactions.append(transaction)

    te = TransactionEncoder()
    te_ary = te.fit(transactions).transform(transactions)
    df = pd.DataFrame(te_ary, columns=te.columns_)

    frequent_itemsets = fpgrowth(df, min_support=0.10, use_colnames=True)
    frequent_itemsets['len'] = frequent_itemsets['itemsets'].apply(lambda x : len(x))
    
    dflen = frequent_itemsets.query("len == 1")
    
    print(tb.tabulate(dflen.sort_values('support', ascending=False), headers='keys', tablefmt='psql'))
    print(len(frequent_itemsets))
    
    lengths = []
    for item in frequent_itemsets.itertuples():
        lengths.append(len(item.itemsets))
    print(Counter(lengths))

    rules = association_rules(frequent_itemsets, metric="confidence", min_threshold=0.50)
    print(f'*** rules ***')
    return rules


def getTechniqueFrequentSequence(cocTTPs : List[List['domain.Technique']], techniques : List['domain.Technique'], tactics : List['domain.Tactic'] ):
    print(f'*** frequent sequence of techniques ***')
    transactions = []

    for cases in cocTTPs:
        transaction = []
        sortedTTPs = sorted(cases, key = lambda t : t.tactics[0].sequence )
        transaction.extend( [x.name for x in sortedTTPs] )
        transactions.append(transaction)


    ps = PrefixSpan(transactions)
    tactics.sort(key=lambda ta : ta.sequence)


    for item in ps.topk(100):
        if len(item[1]) > 2:
            text = ''
            for element in item[1]:
                te = next( (x for x in techniques if x.name == element) )
                ta = next( (x for x in tactics if te in x.techniques) )
                text += f'{te.name}@{ta.name} -->'
            print(text)
    return


def generateGraph(cocTTPs : List[List['domain.Technique']], techniques : List['domain.Technique'], tactics : List['domain.Tactic']) -> nx.Graph:

    df = generateRules(cocTTPs)
    df['alen'] = df['antecedents'].apply(lambda x : len(x)) 
    df['clen'] = df['consequents'].apply(lambda x : len(x)) 
    dfq = df.query("alen == 1 and clen == 1")
    
    ttpsTuples = []

    for row in dfq.itertuples():
        ttpsTuples.append([( list(row.antecedents)[0], list(row.consequents)[0]  ), row.confidence, row.support])

    techniqueNames = [x.id for x in techniques]

    edges = []
    
    for item in ttpsTuples:
        edges.append([(item[0][0], item[0][1]), item[1], item[2]])
              

    cocGraph = nx.Graph()

    for item in edges:
        if item[0][0] not in list(cocGraph.nodes):
            cocGraph.add_node(item[0][0])
        if item[0][1] not in list(cocGraph.nodes):
            cocGraph.add_node(item[0][1])
        
        cocGraph.add_edge(item[0][0], item[0][1], weight = item[1], count = len(cocTTPs) * item[2], distance = 1 - item[1])
    
    for node in cocGraph.nodes():
        cocGraph.nodes[node]['tactic'] = next( (x.tactics[0].id for x in techniques if x.id == node) )
        te = next( (x for x in techniques if x.id == node) )
        cocGraph.nodes[node]['frequency'] = len([x for x in cocTTPs if te in x])
        cocGraph.nodes[node]['title'] = f'{cocGraph.nodes[node]["tactic"]}:{node}'
    
    print(f'number of nodes: {len(cocGraph.nodes)}')
    print(f'number of edges: {len(cocGraph.edges)}')
    
    cocGraph = nx.minimum_spanning_tree(cocGraph, weight='distance')
    
    print(f'number of nodes: {len(cocGraph.nodes)}')
    print(f'number of edges: {len(cocGraph.edges)}')
    
    plt.close()
    nx.draw_spring(cocGraph, with_labels=True, node_color='gold')
    plt.show()
    
    return cocGraph

def generateDiGraph2(cocTTPs : List[List['domain.Technique']], techniques : List['domain.Technique'], tactics : List['domain.Tactic']) -> nx.DiGraph:

    df = generateRules(cocTTPs)
    df['alen'] = df['antecedents'].apply(lambda x : len(x)) 
    df['clen'] = df['consequents'].apply(lambda x : len(x)) 

    dfq = df.query("alen == 1 and clen == 1")
    cofValues = dfq['confidence'].tolist()
    
    print(f'****** {statistics.quantiles(cofValues, n=4)}')

    dfqq = df.query("alen == 2 and clen == 1")
    
    ttpsTuples = []

    for row in dfq.itertuples():
        ttpsTuples.append([( list(row.antecedents)[0], list(row.consequents)[0]  ), row.confidence, row.support])

    techniqueNames = [x.id for x in techniques]

    edges = []
    
    for item in ttpsTuples:
        edges.append([(item[0][0], item[0][1]), item[1], item[2]])
          

    cocDiGraph = nx.DiGraph()

    for item in edges:
        if item[0][0] not in list(cocDiGraph.nodes):
            cocDiGraph.add_node(item[0][0])
        if item[0][1] not in list(cocDiGraph.nodes):
            cocDiGraph.add_node(item[0][1])
        
        cocDiGraph.add_edge(item[0][0], item[0][1], weight = item[1], count = len(cocTTPs) * item[2], distance = 1 - item[1])
    
    alph = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'K', 'L', 'M', 'N', 'O', 'P', 'Q', 'R', 'S', 'T' ]
    idx = 0
    for node in cocDiGraph.nodes():
        cocDiGraph.nodes[node]['tactic'] = next( (x.tactics[0].id for x in techniques if x.id == node) )
        te = next( (x for x in techniques if x.id == node) )
        cocDiGraph.nodes[node]['frequency'] = len([x for x in cocTTPs if te in x])
        cocDiGraph.nodes[node]['title'] = f'{cocDiGraph.nodes[node]["tactic"]}:{node}'
    
    ig = igraph.Graph.from_networkx(cocDiGraph)
    edges = ig.feedback_arc_set()

    tuples = []
    for id in edges:
        source = ig.vs[ig.es[id].source]['_nx_name']
        target = ig.vs[ig.es[id].target]['_nx_name']
        tuples.append((source,target))
    print(f'number of nodes: {len(cocDiGraph.nodes)}')
    print(f'number of edges: {len(cocDiGraph.edges)}')
    
    tacticgroups = list(set(nx.get_node_attributes(cocDiGraph,'tactic').values()))
    plt.figure(3,figsize=(12,8))
    pos = nx.circular_layout(cocDiGraph)
    colors = ['yellow', 'orange', 'cyan', 'gold', 'magenta', 'pink', 'lime']
    shapes = ['d', 'X', 'P']
    shapes = ['o', 'o', 'o']
    tacticnames = []
    for item in tacticgroups:
        tacticnames.append(next( (x.name for x in tactics if x.id == item) ))
    
    labels = [n[1]['title'] for n in cocDiGraph.nodes(data=True)]
    labels = {n[0]: n[1]['title'] for n in cocDiGraph.nodes(data=True)}
    tacticNameLists = [n[1]['tactic'] for n in cocDiGraph.nodes(data=True)]
    print(tacticNameLists)
    print(Counter(tacticNameLists))
    print({n: n for n in cocDiGraph})
    
    
    for index in range(0, len(tacticgroups)):
        searchNodes = [x[0] for x in cocDiGraph.nodes(data=True) if x[1]['tactic'] == tacticgroups[index]]
        nsizes = [cocDiGraph.nodes[x]['frequency']*2000/669 for x in searchNodes]
    
    esizes = []
    for edge in cocDiGraph.edges:
        esizes.append(cocDiGraph.edges[edge[0], edge[1]]["weight"])
    
    nx.draw_networkx_edges(cocDiGraph, pos=pos, width=0.3, edge_color='grey')
    nx.draw_networkx_labels(cocDiGraph,  pos=pos, font_color='blue', font_size=15, font_weight='bold')
    
    plt.legend(scatterpoints = 1)
    ig = igraph.Graph.from_networkx(cocDiGraph)
    
    return cocDiGraph

def normalizeList(values):
    minVal = min(values)
    maxVal = max(values)
    
    newValues = [ (x - minVal)/(maxVal + 0.0000000001 - minVal) for x in values]
    return newValues