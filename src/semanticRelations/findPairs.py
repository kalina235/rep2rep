#import gensim 
#import gensim.downloader as api
#from gensim.models import word2vec
#from gensim.models.word2vec import Word2Vec
import numpy
import nltk
nltk.download('wordnet')
nltk.download('omw-1.4')
from nltk.corpus import wordnet 
wordnet.ensure_loaded()
#!wget https://drive.google.com/file/d/0B7XkCwpI5KDYNlNUTTlSS21pQmM/edit?resourcekey=0-wjGZdNAUop6WykTtMip30g
#vecs = gensim.models.KeyedVectors.load_word2vec_format('vectorSet.bin', binary=True)
#w2v_vocab = set(model.vocab)

#corpus = api.load('text8')
#w2v = word2vec.Word2Vec()
#model = Word2Vec(corpus)

def matchKnowBase(list1, list2):
  scores = numpy.zeros((len(list1),len(list2)))
  for i,l1 in enumerate(list1):
    for j,l2 in enumerate(list2): 
        scores[i][j] = mineWordNet(l1, l2)
  print(scores)
  res = numpy.empty((len(list1)), dtype = object)
  for k in range(len(l1)):
    (i,j) = numpy.unravel_index(scores.argmax(), scores.shape)
    scores[i][j] = -1
    score = scores[i,:]
    res[i] = (int(max(score)*10+1),list1[i], list2[j])
    scores[:,j] = 0
    scores[i,:] = 0
  return res

def mineWordNet(word1, word2, n=0):
   return numpy.max([w1.path_similarity(w2)  for w1 in wordnet.synsets(word1)[::3] for w2 in wordnet.synsets(word2)][::3])
  #return numpy.max([w1.lch_similarity(w2) + w1.wup_similarity(w2) + w1.path_similarity(w2)  for w1 in wordnet.synsets(word1, pos = tag) for w2 in wordnet.synsets(word2, pos = tag)] for tag in [wordnet.NOUN, wordnet.VERB, wordnet.ADJ])

def fileToKnowBases(file1 = "measStickBase", file2 = "motionPathBase"):
  f1 = open(file1, "r")
  f2 = open(file2, "r")
  list1= [word.lower() for line in f1 for word in line.split()]
  list2= [word.lower() for line in f2 for word in line.split()]
  #vocab = model.wv.vocab
  list1 =[l1 for l1 in list1 if len(wordnet.synsets(l1))]
  list2 =[l2 for l2 in list2 if len(wordnet.synsets(l2))]
  return (numpy.array(list1), numpy.array(list2))

def pairsToTschemas(file = "pairedTypes", file1 = "measStickBase", file2 = "motionPathBase"):
  (list1, list2) = fileToKnowBases(file1, file2)
  pairs = matchKnowBase(list1, list2)
  pairs = [x for x in pairs if x!= None]
  print("pairs", pairs)
  for (s,w1,w2) in pairs:
    print(f"tSchema semanticSimilarity{w1}:(measStickG,motionPathG,interMeasPath) = \nsource t:{w1}:universal\ntarget t':{w2}:universal\nantecedent \nconsequent :metaTrue <-analogy[t:further, t':extend]\n strength {s}")
  with open(file, 'w') as fp:
    fp.write('\n\n'.join([f"tSchema semanticSimilarity{w1}:(measStickG,motionPathG,interMeasPath) = \nsource t:{str(w1)}: universal\ntarget t':{str(w2)}: universal \nantecedent \nconsequent :metaTrue <-analogy[t:further, t':extend]\n strength {str(s)}" for (s,w1,w2) in pairs]))
  fp.close()