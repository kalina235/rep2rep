import numpy
import nltk
import math
nltk.download('wordnet')
nltk.download('omw-1.4')
from nltk.corpus import wordnet 
wordnet.ensure_loaded()
#wordnet
import gensim 
import gensim.downloader as api
from gensim.models import word2vec
from gensim.models.word2vec import Word2Vec
vecs = api.load('glove-twitter-25')
corpus = api.load('text8')
w2v = word2vec.Word2Vec()
model = Word2Vec(corpus)
w2v_vocab = set(model.vocab)
#word2vec
#get DS from https://drive.google.com/file/d/0B7XkCwpI5KDYNlNUTTlSS21pQmM/edit?resourcekey=0-wjGZdNAUop6WykTtMip30g, save it as vectors.bin here

import nltk
wordnet_ic = nltk.download('wordnet_ic')
from nltk.corpus import wordnet_ic

import os
f = open("words/Phase1Answers-10a.txt", "r")
leftByFile = {}
rightByFile = {}
wordToFile = {}
allLeft = []
allRight = []
directory='words'
for filename in os.listdir('words'):
    f = os.path.join(directory, filename)
    # checking if it is a file
    
    if os.path.isfile(f):
        print(f)
        leftByFile[f] = []
        rightByFile[f] = []
        file = open(f,'r')
        for line in file:
          words = line.split(':')
          wordL = words[0][1:]
          wordR = words[1][0:-2]
          allLeft.append(wordL)
          allRight.append(wordR)
          leftByFile[f].append(wordL)
          rightByFile[f].append(wordR)
          wordToFile[wordL] = f
          wordToFile[wordR] = f
          #print(wordR)

def scoreParams(a,b,c,wordsLeft, wordToFile):
  pairScores = {}
  score = 0
  for word in wordsLeft:
    pairScores[word] = []
    for wordR in wordsLeft:
      pairScores[word].append((-sim(a,b,c,word,wordR),wordR))
    pairScores[word].sort()
    if(wordToFile[pairScores[word][0][1]] == wordToFile[word]):
      score+=1
  return score*2 #only need one side of the pair to match :)

def scoreBoth(a,b,c,wordsLeft, wordsRight, wordToFile):
  return scoreParams(a,b,c,wordsLeft,wordToFile)+scoreParams(a,b,c,wordsRight,wordToFile)

def gridSearch(wordsLeft, wordsRight, wordToFile):
  results = []
  for a in range(0,20):
    af = a/2
    # for b in range(0,20-a):
    bf = 10-af
    c=10-af-bf
    results.append((-scoreBoth(af,bf,c,wordsLeft,wordsRight,wordToFile),(af,bf,c)))
    print(results)
  results.sort()
  return results

results = gridSearch(allLeft,allRight,wordToFile)
print(results)


def wupScore(w1, w2):
   for synset in wordnet.synsets(w1):
    # print(synset)
    # print(w2)]
      for synset2 in wordnet.synsets(w2):
        return synset.wup_similarity(synset2)
      return 0
   return 0
   
def pathScore(w1, w2):
  for synset in wordnet.synsets(w1):
    if synset.pos == wordnet.VERB:
      for synset2 in wordnet.synsets(w2):
        if synset2.pos == wordnet.VERB:
          print(synset.pos)
          return synset.path_similarity(synset2)
      return 0
  return 0

def word2vecsc(word1, word2):
   return model.wv.similarity(w1, w2)

def sim(a,b,c,w1,w2):
  if w1 == w2:
    return a+b+c
  # vocab = model.wv.vocab
  score = 0.2
  # if w1 in vocab:
    # if w2 in vocab:
  return a*wupScore(w1, w2)+b*pathScore(w1,w2)
      # +c*word2vecsc(w1,w2)
  return 0

def paramscore(a, b, c, t, u, corp):
  for i,w1 in enumerate(t): 
    for j,w2 in enumerate(u):
      wordmatch[i][j]  = sim(a,b,c,w1,w1)
  for i in range(len(t)+len(u)):
      (k,l) = argmax(wordmatch)
      if (t[k], u[l]) in gt or (t[l], u[k]) in gt:
          score+=1
          wordmatch[k][:] = 0
          wordmatch[:][l] = 0
  return score

def optimParam(t, u):
  best = [(0,0,0)]*10
  for i in range(0,10, step = 0.5):
    for j in range(0,10, step = 0.5):
      k = 30-i-j
      parScore[i][j][k] = paramScore(a,b,c,t,u,corp)
  for i in range(10):
    best[i]= maxarg(parScore) #set macro
    parScore[maxarg] = 0
  return best

def decideModel(best, gt, gu):
  for (a,b,c) in best:
    evals[a,b,c] = paramscore(a,b,c,gt,gu,corp)
  return maxarg(evals)

#plot in 3d