import numpy
import gensim 
import gensim.downloader as api
from gensim.models import word2vec
from gensim.models.word2vec import Word2Vec
#!wget https://drive.google.com/file/d/0B7XkCwpI5KDYNlNUTTlSS21pQmM/edit?resourcekey=0-wjGZdNAUop6WykTtMip30g
#vecs = gensim.models.KeyedVectors.load_word2vec_format('vectorSet.bin', binary=True)
#w2v_vocab = set(model.vocab)

corpus = api.load('text8')
w2v = word2vec.Word2Vec()
model = Word2Vec(corpus)

def matchKnowBase(list1, list2):
  pairs = []
  scores = numpy.zeros((len(list1), len(list2)))
  for i,l1 in enumerate(list1):
    for j,l2 in enumerate(list2): 
        scores[i][j] = model.wv.similarity(l1,l2)
  while(numpy.amax(scores) > 0):
    (i,j) = numpy.unravel_index(scores.argmax(), scores.shape)
    fs = [i for (i,j) in pairs]
    ss = [j for (i,j) in pairs]
    if list1[i] not in fs and list2[j] not in ss:
      pairs.append((list1[i], list2[j]))
    scores[i][j] = -1
  return pairs

def fileToKnowBases(file1 = "measStickBase.txt", file2 = "motionPathBase.txt"):
  f1 = open(file1, "r")
  f2 = open(file2, "r")
  list1= [word.lower() for line in f1 for word in line.split()]
  list2= [word.lower() for line in f2 for word in line.split()]
  vocab = model.wv.vocab
  list1 =[l1 for l1 in list1 if l1 in vocab]
  list2 =[l2 for l2 in list2 if l2 in vocab]
  return (numpy.array(list1), numpy.array(list2))

def returnPairs(file1 = "measPathBase", file2 = "motionPathBase"):
  (list1, list2) = fileToKnowBases(file1, file2)
  return matchKnowBase(list1, list2)

def fileToKnowBases(file1 = "measStickBase", file2 = "motionPathBase"):
  f1 = open(file1, "r")
  f2 = open(file2, "r")
  list1= [word.lower() for line in f1 for word in line.split()]
  list2= [word.lower() for line in f2 for word in line.split()]
  vocab = model.wv.vocab
  list1 =[l1 for l1 in list1 if l1 in vocab]
  list2 =[l2 for l2 in list2 if l2 in vocab]
  return (numpy.array(list1), numpy.array(list2))

def similarPairs(file1 = "measStickBase", file2 = "motionPathBase"):
  (list1, list2) = fileToKnowBases(file1, file2)
  return matchKnowBase(list1, list2)

def pairsToFile(file = "pairedTypes", file1 = "measStickBase", file2 = "motionPathBase"):
  pairs = similarPairs(file1, file2)
  with open(file, 'w') as fp:
    fp.write('\n'.join('%s %s' % x for x in pairs))
  fp.close()
pairsToFile()