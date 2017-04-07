import akka.actor.{ActorRef, Props, Actor, ActorSystem,Terminated}
import java.security.MessageDigest
import scala.collection.mutable.ListBuffer

/**
 * Created by mayank on 10/18/15.
 */

case class UpdatePre(n: ActorRef)

case class UpdateOthers(n: ActorRef, hash: BigInt, prev: BigInt, i: Int)

case class SearchAKey(key: BigInt, hops: Int, n: ActorRef, totalMessages: Int, orig: ActorRef, flag: Boolean)

case class ShowResult(key: BigInt, pred: ActorRef, succ: ActorRef, step: Int, n: ActorRef, origTotalMessages: Int,  flag: Boolean)

//case object DisplaySystem

case class UpdateSucc(n: ActorRef)

case class InitFingerSucc(start: BigInt, n: ActorRef, i: Int)

case class UpdateAFinger(succ: ActorRef, i: Int)

case class JoinNewNode(bootstrapNode: ActorRef)

case class FindPredecessor(n: ActorRef, hash: BigInt)

case class YourPredecessor(pre: ActorRef, succ: ActorRef)

case class FindAverageHops(key: BigInt, hops: Int, n: ActorRef, totalMessages: Int, orig: ActorRef, flag: Boolean)

case class getSuccessorList()

case class receiveSuccessorList(successorList: ListBuffer[ActorRef])

case class updateSuccessorList(successorList: ListBuffer[ActorRef], count: Int)

case class fixFingerTable(successor:ActorRef, hashaddr: BigInt, deleted: ActorRef)

case class getHashAddress()

case class sendHashAddress(hashAddr: BigInt)

case class UpdateOthersTolerent(n: ActorRef, hash: BigInt, prev: BigInt, i: Int,deleted: ActorRef)


object ChordMain extends App {
  override def main(args: Array[String]) {
    val chordSystem = ActorSystem("chordImplActSystem")
    var totalNodes = 0
    var totalMessages = 0
    var killedNodes: Int = 0;
    var terminated=0
    if(args.length == 2) {
      totalNodes = args(0).toInt
      totalMessages = args(1).toInt
      if(totalNodes<=0){
        println ("Number of nodes should be greater than 0" )
      }
      if(totalMessages<=0){
        println ("Number of messages should be greater than 0" )
      }
    }else{
      println ("Not Correct Arguments" )
      chordSystem.shutdown()
    }
    var nodes = Array.ofDim[ActorRef](totalNodes)
    val random = scala.util.Random
    val node0 = chordSystem.actorOf(Props(new Node(0)), name = "0")
    var isKilled = new Array[Boolean](totalNodes)
    for(i <- 0 to totalNodes-1)
      isKilled(i) = false

    if(totalNodes>0){

      nodes(0) = node0
    }
    if (totalNodes > 1) {
      for (i <- 1 to totalNodes - 1) {
        nodes(i) = chordSystem.actorOf(Props(new Node(i)), name = i.toString)
        nodes(i) ! JoinNewNode(node0)
        Thread.sleep(100)
      }
    }


    //set this flag to true to test the Failure model
    //We are killing nodes which have id's multiple of 20
    val bonusKillANode: Boolean = false

    if (totalMessages > 0 && totalNodes>1) {
      for (i <- 0 until totalNodes) {
        for(j<-0 until totalMessages){
          Thread.sleep(1000)
          //    val randomNodeId = random.nextInt(totalNodes - 1)
          val randomKey = random.nextInt(100000)
          val digest: String = MessageDigest.getInstance("SHA-1").digest(randomKey.toString.getBytes("UTF-8")).map("%02x".format(_)).mkString
          //  val node = nodes(randomNodeId)
          if(i > 0 && i < totalNodes - 4 && bonusKillANode){
            if(i % 20 == 0){
              if(!isKilled(i)){
                nodes(i) ! "kill"
                killedNodes += 1
                isKilled(i) = true
                Thread.sleep(500)
              }
            }}
          if(!isKilled(i)){
            if(i == totalNodes - 1 && j == totalMessages - 1)
              node0 ! FindAverageHops(BigInt.apply(digest,16), 0, nodes(i), totalMessages*(totalNodes-killedNodes), node0, true)
            else
              node0 ! FindAverageHops(BigInt.apply(digest,16), 0, nodes(i), totalMessages*(totalNodes-killedNodes), node0, false)
          }
        }
      }
    }else{
      if(totalNodes==1){
        for (i <- 0 until totalMessages) {
          Thread.sleep(20)
          node0 ! FindAverageHops(0, 0, node0, totalMessages, node0, true)
        }

      }
    }
       chordSystem.awaitTermination()
  }
}

class Node(myHashAddr: BigInt) extends Actor {

  var hopsCounter: Int = 0
  var messageCounter: Int = 0
  val myHashAddress: BigInt = returnHashCode(myHashAddr)
  val m = 160
  var successHashAddress: BigInt = myHashAddr
  var succList = new ListBuffer[ActorRef]()   // Failure Handle
  var myPredecessor = self
  var mySuccessor = self
  var bootstrap: ActorRef = null
  var fingerTableArray = new Array[ActorRef](m)

  def returnHashCode(id: BigInt): BigInt = {
    val digest: String = MessageDigest.getInstance("SHA-1").digest(id.toString.getBytes("UTF-8")).map("%02x".format(_)).mkString
    return BigInt.apply(digest, 16)
  }

  def getStartOfFinger(i: Int): BigInt = {
    val power = BigInt(2).pow(i)
    val powerEnd = BigInt(2).pow(m)
    val x = (myHashAddress + power) % powerEnd
    return x
  }


  def isInRange(a: BigInt, beg: BigInt, end: BigInt): Boolean = {
    if (beg == end) {
      if (a == beg) {
        return false
      } else {
        return true
      }
    } else if (beg < end) {
      if (a > beg && a < end) {
        return true
      } else {
        return false
      }
    } else {
      if (a > beg || a < end) {
        return true
      } else {
        return false
      }
    }
  }

  def isInRangeLeft(a: BigInt, beg: BigInt, end: BigInt): Boolean = {
    if (beg == end) {
      return true
    } else if (beg < end) {
      if (a >= beg && a < end) {
        return true
      } else {
        return false
      }
    } else {
      if (a >= beg || a < end) {
        return true
      } else {
        return false
      }
    }
  }

  def isInRangeRight(a: BigInt, beg: BigInt, end: BigInt): Boolean = {
    if (beg == end) {
      return true
    } else if (beg < end) {
      if (a > beg && a <= end) {
        return true
      } else {
        return false
      }
    } else {
      if (a > beg || a <= end) {
        return true
      } else {
        return false
      }
    }
  }

  def isInRangeBoth(a: BigInt, beg: BigInt, end: BigInt): Boolean = {
    if (beg == end) {
      return true
    } else if (beg < end) {
      if (a >= beg && a <= end) {
        return true
      } else {
        return false
      }
    } else {
      if (a >= beg || a <= end) {
        return true
      } else {
        return false
      }
    }
  }


  def precedingFinger(id: BigInt): ActorRef = {
    for (i <- (m - 1) to 0 by -1) {
      if (isInRange(returnHashCode(fingerTableArray(i).path.name.toInt), myHashAddress, id)) {
        return fingerTableArray(i)
      }
    }
    return self
  }

  //initializing all fingers in fingerTableArray to myself by default
  for (i <- 0 to m - 1) {
    fingerTableArray(i) = self
  }

  for(i <- 0 to 6){
    succList += self
  }
  override def receive: Receive = {

    case FindPredecessor(a, addr) => {
      if (isInRangeRight(addr, myHashAddress, returnHashCode(fingerTableArray(0).path.name.toInt))) {
        a ! YourPredecessor(self, mySuccessor)
      } else {
        val x = precedingFinger(addr)
        x ! FindPredecessor(a, addr)
      }
    }
    case UpdateSucc(x) => {
      mySuccessor = x
      if(mySuccessor != self){
     /*   println("--------------------------------------------")
        println("The Watched", x.path.name)
        println("The Watcher", self.path.name)*/
        context.watch(x)
      }
      x ! getHashAddress()
      x ! getSuccessorList()
      List()
    }
    case getSuccessorList() => {
      sender ! receiveSuccessorList(succList)
    }
    case getHashAddress() =>{
      /*println ("Asking for Hash: ", myHashAddress)*/
      sender ! sendHashAddress(myHashAddress)
    }

    case sendHashAddress(suchashaddr : BigInt) =>{
      successHashAddress = suchashaddr
    }

    case receiveSuccessorList(successorList: ListBuffer[ActorRef]) => {
      succList = successorList
      succList = succList.dropRight(1)
      succList.insert(0, sender)
      /*if (self != sender)
        context.watch(sender)*/
      myPredecessor ! updateSuccessorList(succList, 1)
    }

    case updateSuccessorList(successorList: ListBuffer[ActorRef], count: Int) => {
      if(count < 6){
        succList = successorList
        succList = succList.dropRight(1)
        succList.insert(0, sender)
        /*if (self != sender)
          context.watch(sender)*/
        myPredecessor ! updateSuccessorList(succList, count+1)
      }
    }
    case fixFingerTable(successor:ActorRef, hashaddr: BigInt, deleted: ActorRef) =>{
      for (i <- 0 to m - 1) {
        val power = BigInt(2).pow(i)-1
        val powerEnd = BigInt(2).pow(m)
        val others = (hashaddr+powerEnd-power) % powerEnd
        self ! UpdateOthersTolerent(successor, hashaddr, others, i,deleted)
      }
    }
    case UpdateOthersTolerent(n, s, prev, i,deleted) => {
      if (deleted != self && sender != n) {
        if(fingerTableArray(i)==deleted){
          fingerTableArray(i)=n
          myPredecessor ! UpdateOthersTolerent(n, s, myHashAddress, i, deleted)
        }
      }
    }

    case YourPredecessor(pre, succ) => {
      myPredecessor = pre
      mySuccessor = succ
      if(mySuccessor != self)
        context.watch(mySuccessor)
      succ ! getHashAddress()
      succ ! getSuccessorList()
      pre ! UpdateSucc(self)
      succ ! UpdatePre(self)
      fingerTableArray(0) = mySuccessor
      for (i <- 0 to m - 2) {
        if (isInRangeBoth(getStartOfFinger(i + 1), myHashAddress, returnHashCode(fingerTableArray(i).path.name.toInt))) {
          fingerTableArray(i + 1) = fingerTableArray(i)
        }
        else {
          if (bootstrap != null) {
            bootstrap ! InitFingerSucc(getStartOfFinger(i + 1), self, i + 1)
          }
        }
      }
      for (i <- 0 to m - 1) {
        val power = BigInt(2).pow(i) - 1
        val powerEnd = BigInt(2).pow(m)
        val others = (myHashAddress + powerEnd - power) % powerEnd
        mySuccessor ! UpdateOthers(self, myHashAddress, others, i)
      }
    }
    case JoinNewNode(boot) => {
      bootstrap = boot
      bootstrap ! FindPredecessor(self, myHashAddress)
    }
    case UpdatePre(x) => {
      myPredecessor = x
    }
    case UpdateOthers(n, s, prev, i) => {
      if (n != self) {
        if (isInRangeRight(prev, myHashAddress, returnHashCode(fingerTableArray(0).path.name.toInt))) {
          if (isInRange(s, myHashAddress, returnHashCode(fingerTableArray(i).path.name.toInt))) {
            fingerTableArray(i) = n
            myPredecessor ! UpdateOthers(n, s, myHashAddress, i)
          }
        } else {
          val x = precedingFinger(prev)
          x ! UpdateOthers(n, s, prev, i)
        }
      }
    }

    case UpdateAFinger(succ, i) => {
      fingerTableArray(i) = succ
    }

    case InitFingerSucc(id, n, i) => {
      if (isInRangeRight(id, myHashAddress, returnHashCode(fingerTableArray(0).path.name.toInt))) {
        n ! UpdateAFinger(mySuccessor, i)
      } else {
        val x = precedingFinger(id)
        x ! InitFingerSucc(id, n, i)
      }
    }
    case FindAverageHops(key, hops, n, origTotalMessages, orig, flag) =>
      n ! SearchAKey(key, hops, n, origTotalMessages, orig, flag)
    case SearchAKey(key, hops, n, origTotalMessages, orig, flag) => {
      // println("key="+key+"myHashAddress="+myHashAddress++"secc hash="+fingerTableArray(0).path.name.toInt)
      if (isInRangeRight(key, myHashAddress, returnHashCode(fingerTableArray(0).path.name.toInt))) {


        orig ! ShowResult(key, self, mySuccessor, hops, n, origTotalMessages, flag)
      } else {
        val x = precedingFinger(key)
        // println("node="+x.path.name)
        x ! SearchAKey(key, hops + 1, n, origTotalMessages, orig, flag)
      }
    }

    case ShowResult(key, pre, succ, hops, n, origTotalMessages, flag) => {
      hopsCounter = hopsCounter + hops
      messageCounter = messageCounter + 1
     /* println("node n="+n.path.name+" key:" + key +" suc:" + succ.path.name +
        "Hops:" + hops + ": counter=" + messageCounter + ":totalHops=" + hopsCounter)*/
      if (flag) {
        val average: Float = (hopsCounter.toFloat / origTotalMessages)
        println("Average number of hops to deliver a message = " + average)
      }

    }

    case "kill" =>

      context.stop(self)
    case Terminated(child) => {
      if(mySuccessor.path.name == child.path.name){
      /*  println("************************** Terminated Receive *******************")
        println("The Actor Name"+child.path.name)
        println("The Watcher Name"+ self.path.name)
        println ("The Actor List"+ succList)*/
        succList = succList.drop(1)
        var temp = succList(0)
       // println ("The Successor Next", temp.path.name)
        var oldSuccessorAddress = successHashAddress
        /*println ("Old hashaddr", oldSuccessorAddress)*/
        temp ! getHashAddress()
        val oldSuccessor = mySuccessor
        mySuccessor = succList(0)
        if(mySuccessor != self)
          context.watch(mySuccessor)
        fingerTableArray(0) = succList(0)
        succList(0) ! UpdatePre(self)
        self ! fixFingerTable(succList(0),oldSuccessorAddress, child)
        myPredecessor ! updateSuccessorList(succList, 0)
      }
    }

  }
}