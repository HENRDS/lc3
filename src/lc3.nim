
type
  Opcode = enum
    opBr, opAdd, opLd, opSt, opJsr, opAnd, opLdr, opStr, opRti, opNot, opLdi, opSti, opJmp, opRes, opLea, opTrap 
  Register = enum
    r0, r1, r2, r3, r4, r5, r6, r7, rIp, rCond
  Ptr = distinct uint16
  VmObject = object
    memory: array[Ptr, uint16]
    registers: array[Register, uint16]
    isHalted: bool
  Vm = ptr VmObject

const 
  IpStart = uint16(0x3000)
  # Flags
  FlagPositive = 1
  FlagZero = 1 shl 1
  FlagNegative = 1 shl 2
  # Traps
  TrapGetc = 0x20
  TrapOut = 0x21
  TrapPuts = 0x22
  TrapIn = 0x23
  TrapPutSp = 0x24
  TrapHalt = 0x25

proc `+`(a, b: Ptr): Ptr {.borrow.}

proc createVm(): Vm =
  result = create(VmObject)
  result.isHalted = false
  result.registers[rIp] = IpStart

proc destroyVm(vm: Vm)=
  dealloc(vm)

proc signExtend(x: uint16, bitCount: Positive): uint16 =
  result = x
  if ((x shr (bitCount - 1)) and 1) == 1:
    result = (uint16(0xFFFF) shl bitCount)


proc updateFlags(vm: Vm, r: Register) =
  let v = vm.registers[r]
  if v == 0:
    vm.registers[rCond] = FlagZero
  elif ((v shr 15) and 1) == 1:
    vm.registers[rCond] = FlagNegative
  else:
    vm.registers[rCond] = FlagPositive


proc run(vm: Vm)=
  while not vm.isHalted:
    let instr = vm.memory[Ptr(vm.registers[rIp])]
    inc(vm.registers[rIp])
    try:
      let op = Opcode(instr shr 12)
      case op:
      of opBr:
        let 
          ipOffset = signExtend(instr and 0x1FF, 9)
          condFlag = (instr shr 9) and 7
        if (condFlag and vm.registers[rCond]) > 0:
          vm.registers[rIp] += ipOffset 
      of opAdd:
        let 
          dest = Register((instr shr 9) and 7)
          reg0 = Register((instr shr 6) and 7)
          immFlag = (instr shr 5) and 1
        if (immFlag == 1):
          let immediate = signExtend(instr and 0x1F, 5)
          vm.registers[dest] = vm.registers[reg0] + immediate
        else:
          let reg1 = Register(instr and 7)
          vm.registers[dest] = vm.registers[reg0] + vm.registers[reg1]
        vm.updateFlags(dest)
      of opLd:
        let 
          reg0 = Register((instr shr 9) and 7)
          ipOffset = signExtend(instr and 0x1FF, 9)
        vm.registers[reg0] = vm.memory[Ptr(vm.registers[rIp] + ipOffset)]
        vm.updateFlags(reg0)
      of opSt:
        let
          reg0 = Register((instr shr 9) and 7)
          ipOffset = signExtend(instr and 0x1FF, 9)
        vm.memory[Ptr(vm.registers[rIp] + ipOffset)] = vm.registers[reg0]
      of opJsr:
        let longFlag = ((instr shr 11) and 1) == 1
        vm.registers[r7] = vm.registers[rIp]
        if longFlag:
          let longIpOffset = signExtend(instr and 0x7FF, 11)
          vm.registers[rIp] += longIpOffset;
        else:
          let reg1 = Register((instr shr 6) and 7)
          vm.registers[rIp] = vm.registers[reg1]
      of opAnd:
        let 
          dest = Register((instr shr 9) and 7)
          reg0 = Register((instr shr 6) and 7)
          immFlag = (instr shr 5) and 1
        if (immFlag == 1):
          let immediate = signExtend(instr and 0x1F, 5)
          vm.registers[dest] = vm.registers[reg0] and immediate
        else:
          let reg1 = Register(instr and 7)
          vm.registers[dest] = vm.registers[reg0] and vm.registers[reg1]
        vm.updateFlags(dest)
      of opLdr:
        let 
          reg0 = Register((instr shr 9) and 7)
          reg1 = Register((instr shr 6) and 7)
          offset = signExtend(instr and 0x3F, 6)
        vm.registers[reg0] = vm.memory[Ptr(vm.registers[reg1] + offset)]
        vm.updateFlags(reg0)
      of opStr:
        let
          reg0 = Register((instr shr 9) and 7)
          reg1 = Register((instr shr 6) and 7)
          offset = signExtend(instr and 0x3F, 6)
        vm.memory[Ptr(vm.registers[reg1] + offset)] = vm.registers[reg0]
      of opNot:
        let 
          dest = Register((instr shr 9) and 7)
          reg0 = Register((instr shr 6) and 7)
        vm.registers[dest] = not vm.registers[reg0]
        vm.updateFlags(dest)
      of opLdi:
        let 
          dest = Register((instr shr 9) and 7)
          ipOffset = signExtend(instr and 0x1FF, 9)
        vm.registers[dest] = vm.memory[Ptr(vm.memory[Ptr(vm.registers[rIp] + ipOffset)])]
        vm.updateFlags(dest)
      of opSti:
        let
          reg0 = Register((instr shr 9) and 7)
          ipOffset = signExtend(instr and 0x1FF, 9)
        vm.memory[Ptr(vm.memory[Ptr(vm.registers[rIp] + ipOffset)])] = vm.registers[reg0]
      of opJmp:
        let longFlag = (instr shr 11) and 1
        vm.registers[r7] = vm.registers[rIp]
        if longFlag == 1:
          let longIpOffset = signExtend(instr and 0x7FF, 11)
          vm.registers[rIp] += longIpOffset
        else:
          let reg0 = Register((instr shr 6) and 7)
          vm.registers[rIp] = vm.registers[reg0]
      of opLea:
        let
          reg0 = Register((instr shr 9) and 7)
          ipOffset = signExtend(instr and 0x1FF, 9)
        vm.memory[Ptr(vm.registers[rIp] + ipOffset)] = vm.registers[reg0]
      of opTrap:
        case instr and 0xFF
        of TrapGetc:
          let c = stdin.readChar()
          vm.registers[r0] = uint16(c)
        of TrapOut:
          let c = vm.registers[r0]
          stdout.write(c)
          stdout.flushFile()
        of TrapPuts:
          var p = Ptr(vm.registers[r0])
          while vm.memory[p] != 0:
            stdout.write(char(vm.memory[p]))
            p = p + Ptr(1)
          stdout.flushFile()
        of TrapIn:
          stdout.write("Enter a character: ")
          let c = stdin.readChar()
          vm.registers[r0] = uint16(c)
        of TrapPutSp:
          var p = Ptr(vm.registers[r0])
          while vm.memory[p] != 0:
            let 
              word = vm.memory[p]
              c1 = char(word and 0xFF)
              c2 = char(word shr 8)
            stdout.write(c1)
            if c2 != '\0':
              stdout.write(c2)
            p = p + Ptr(1)
        of TrapHalt:
          stdout.writeLine("HALT")
          vm.isHalted = true
        else:
          stdout.writeLine("Invalid trap: " & $(instr and 0xFF))
          vm.isHalted = true
      of opRes, opRti:
        discard
    except Exception as e:
      echo e.msg
      vm.isHalted = true

proc readImage(vm: Vm, file: File)=
  discard

proc main()=
  # Load Args
  let vm = createVm()
  defer: vm.destroyVm()
  discard

when isMainModule:
  main()