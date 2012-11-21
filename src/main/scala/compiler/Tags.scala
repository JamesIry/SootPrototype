package compiler

import soot.tagkit._
import soot.jimple.toolkits.annotation.tags._

class FreshTag extends Tag {
  var value = 0
  override def getName = "FreshTag"
  override def getValue = 
      Array[Byte](
      ((value >> 24) & 0xff).asInstanceOf[Byte],
      ((value >> 16) & 0xff).asInstanceOf[Byte],
      ((value >>  8) & 0xff).asInstanceOf[Byte],
      ((value      ) & 0xff).asInstanceOf[Byte]
  )
}

object BoxTag extends Tag with OneByteCodeTag {
  override def getName = "BoxTag"
  override def getValue = Array(0)
}

object UnboxTag extends Tag with OneByteCodeTag {
  override def getName = "UnBoxTag"
  override def getValue = Array(0)
}