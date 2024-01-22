package compiler

import (
	"fmt"
	"monkey/ast"
	"monkey/code"
	"monkey/object"
)

type Bytecode struct {
	Instructions code.Instructions
	Constants    []object.Object
}

type EmittedInstruction struct {
	Opcode   code.OpCode
	Position int
}

type Compiler struct {
	instructions    code.Instructions
	constants       []object.Object
	lastInstruction EmittedInstruction
	prevInstruction EmittedInstruction
	symbolTable     *SymbolTable
}

func New() *Compiler {
	return &Compiler{
		instructions:    code.Instructions{},
		constants:       []object.Object{},
		lastInstruction: EmittedInstruction{},
		prevInstruction: EmittedInstruction{},
		symbolTable:     NewSymbolTable(),
	}
}

func NewWithState(symbolTable *SymbolTable, constants []object.Object) *Compiler {
	compiler := New()
	compiler.symbolTable = symbolTable
	compiler.constants = constants
	return compiler
}

func (c *Compiler) Bytecode() *Bytecode {
	return &Bytecode{
		Instructions: c.instructions,
		Constants:    c.constants,
	}
}

func (c *Compiler) Compile(node ast.Node) error {
	switch node := node.(type) {
	case *ast.Program:
		for _, statement := range node.Statements {
			err := c.Compile(statement)
			if err != nil {
				return err
			}
		}
	case *ast.ExpressionStatement:
		err := c.Compile(node.Expression)
		if err != nil {
			return err
		}
		c.emit(code.OpPop)
	case *ast.IntegerLiteral:
		integer := &object.Integer{
			Value: node.Value,
		}
		c.emit(code.OpConstant, c.addConstant(integer))
	case *ast.InfixExpression:

		if node.Operator == "<" {
			err := c.Compile(node.Right)
			if err != nil {
				return err
			}

			err = c.Compile(node.Left)
			if err != nil {
				return err
			}
			c.emit(code.OpGreaterThan)
			return nil
		}

		err := c.Compile(node.Left)
		if err != nil {
			return err
		}
		err = c.Compile(node.Right)
		if err != nil {
			return err
		}
		switch node.Operator {
		case "+":
			c.emit(code.OpAdd)
		case "-":
			c.emit(code.OpSub)
		case "*":
			c.emit(code.OpMul)
		case "/":
			c.emit(code.OpDiv)
		case ">":
			c.emit(code.OpGreaterThan)
		case "==":
			c.emit(code.OpEqual)
		case "!=":
			c.emit(code.OpNotEqual)
		default:
			return fmt.Errorf("unknown operator %s", node.Operator)
		}
	case *ast.Boolean:
		if node.Value {
			c.emit(code.OpTrue)
		} else {
			c.emit(code.OpFalse)
		}
	case *ast.PrefixExpression:
		err := c.Compile(node.Right)
		if err != nil {
			return err
		}

		switch node.Operator {
		case "!":
			c.emit(code.OpBang)
		case "-":
			c.emit(code.OpMinus)
		default:
			return fmt.Errorf("unknown operator %s", node.Operator)
		}
	case *ast.IfExpression:
		err := c.Compile(node.Condition)
		if err != nil {
			return err
		}

		// emit an `OpJumpNotTruthy` with a bogus value, to be replaced later
		jumpNotTruthyPosition := c.emit(code.OpJumpNotTruthy, 9999)
		err = c.Compile(node.Consequence)
		if err != nil {
			return err
		}

		if c.lastInstructionIsPop() {
			c.removeLastPop()
		}

		jumpPosition := c.emit(code.OpJump, 9999)
		afterConsequencePosition := len(c.instructions)
		c.changeOperand(jumpNotTruthyPosition, afterConsequencePosition)

		if node.Alternative == nil {
			c.emit(code.OpNull)
		} else {
			err = c.Compile(node.Alternative)
			if err != nil {
				return err
			}

			if c.lastInstructionIsPop() {
				c.removeLastPop()
			}
		}

		afterAlternativePosition := len(c.instructions)
		c.changeOperand(jumpPosition, afterAlternativePosition)

	case *ast.BlockStatement:
		for _, statement := range node.Statements {
			err := c.Compile(statement)
			if err != nil {
				return err
			}
		}
	case *ast.LetStatement:
		err := c.Compile(node.Value)
		if err != nil {
			return err
		}

		symbol := c.symbolTable.Define(node.Name.Value)
		c.emit(code.OpSetGlobal, symbol.Index)
	case *ast.Identifier:
		symbol, ok := c.symbolTable.Resolve(node.Value)
		if !ok {
			return fmt.Errorf("undefined variable %s", node.Value)
		}
		c.emit(code.OpGetGlobal, symbol.Index)
	}

	return nil
}

func (c *Compiler) lastInstructionIsPop() bool {
	return c.lastInstruction.Opcode == code.OpPop
}

func (c *Compiler) removeLastPop() {
	c.instructions = c.instructions[:c.lastInstruction.Position]
	c.lastInstruction = c.prevInstruction
}

func (c *Compiler) addConstant(obj object.Object) int {
	c.constants = append(c.constants, obj)
	return len(c.constants) - 1
}

func (c *Compiler) replaceInstruction(position int, newInstruction []byte) {
	for i := 0; i < len(newInstruction); i++ {
		c.instructions[position+i] = newInstruction[i]
	}
}

func (c *Compiler) changeOperand(opPosition int, operand int) {
	op := code.OpCode(c.instructions[opPosition])
	newInstruction := code.Make(op, operand)
	c.replaceInstruction(opPosition, newInstruction)
}

func (c *Compiler) emit(op code.OpCode, operands ...int) int {
	instruction := code.Make(op, operands...)
	position := c.addInstruction(instruction)
	c.setLastInstruction(op, position)
	return position
}

func (c *Compiler) addInstruction(instruction []byte) int {
	position := len(c.instructions)
	c.instructions = append(c.instructions, instruction...)
	return position
}

func (c *Compiler) setLastInstruction(op code.OpCode, position int) {
	previous := c.lastInstruction
	last := EmittedInstruction{Opcode: op, Position: position}
	c.prevInstruction = previous
	c.lastInstruction = last
}
