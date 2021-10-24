package antlr

import (
	"bytes"
	"fmt"
	"io"
	"reflect"

	"github.com/emirpasic/gods/lists"
	"github.com/emirpasic/gods/lists/arraylist"
	"github.com/emirpasic/gods/lists/singlylinkedlist"
	"github.com/emirpasic/gods/sets"
	"github.com/emirpasic/gods/sets/hashset"
	"github.com/emirpasic/gods/stacks"
	"github.com/emirpasic/gods/stacks/arraystack"
)

/**
 * JDO returning information about matching tokens and rules
 */
type CandidatesCollection struct {
	/**
	 * Collection of Token ID candidates, each with a follow-on List of
	 * subsequent tokens
	 */
	Tokens map[int][]int

	/**
	 * Collection of Rule candidates, each with the callstack of rules to
	 * reach the candidate
	 */
	Rules map[int][]int

	/**
	 * Collection of matched Preferred Rules each with their start and end
	 * offsets
	 */
	RulePositions map[int][]int
}

func (cc *CandidatesCollection) String() string {
	return fmt.Sprintf("CandidatesCollection{tokens=%v, rules=%v, ruleStrings=%v}", cc.Tokens, cc.Rules, cc.RulePositions)
}

type FollowSetWithPath struct {
	Intervals *IntervalSet
	Path      lists.List
	Following []int
}

type FollowSetsHolder struct {
	Sets     lists.List
	Combined *IntervalSet
}

type PipelineEntry struct {
	State      ATNState
	TokenIndex int
}

func NewPipelineEntry(state ATNState, tokenIndex int) *PipelineEntry {
	return &PipelineEntry{State: state, TokenIndex: tokenIndex}
}

type Vocabulary struct {
	LiteralNames  []string
	SymbolicNames []string
}

type CodeCompletionCore struct {
	showResult                 bool
	showDebugOutput            bool
	debugOutputWithTransitions bool
	showRuleStack              bool

	ignoredTokens  sets.Set
	preferredRules sets.Set

	parser     Recognizer
	atn        *ATN
	vocabulary *Vocabulary
	ruleNames  []string
	tokens     []Token

	tokenStartIndex int
	statesProcessed int

	// A mapping of rule index to token stream position to end token positions.
	// A rule which has been visited before with the same input position will always produce the same output positions.
	shortcutMap     map[int]map[int]sets.Set
	candidates      CandidatesCollection
	followSetsByATN map[string]map[int]*FollowSetsHolder

	log io.Writer
}

func NewCodeCompletionCore(parser Recognizer, preferredRules sets.Set, ignoredTokens sets.Set, log io.Writer) *CodeCompletionCore {
	c3 := &CodeCompletionCore{
		showResult:                 true,
		showDebugOutput:            true,
		debugOutputWithTransitions: true,
		showRuleStack:              true,
		parser:                     parser,
		preferredRules:             preferredRules,
		ignoredTokens:              ignoredTokens,
		atn:                        parser.GetATN(),
		vocabulary: &Vocabulary{
			LiteralNames:  parser.GetLiteralNames(),
			SymbolicNames: parser.GetSymbolicNames(),
		},
		ruleNames:       parser.GetRuleNames(),
		shortcutMap:     map[int]map[int]sets.Set{},
		followSetsByATN: map[string]map[int]*FollowSetsHolder{},
		log:             log,
	}
	if c3.preferredRules == nil {
		c3.preferredRules = hashset.New()
	}
	if c3.ignoredTokens == nil {
		c3.ignoredTokens = hashset.New()
	}
	return c3
}

func (c3 *CodeCompletionCore) GetPreferredRules() sets.Set {
	return hashset.New(c3.preferredRules.Values()...)
}

func (c3 *CodeCompletionCore) SetPreferredRules(r sets.Set) {
	c3.preferredRules = r
}

// CollectCandidates is the main entry point. The caret token index specifies the token stream index for the token which currently
// covers the caret (or any other position you want to get code completion candidates for).
// Optionally you can pass in a parser rule context which limits the ATN walk to only that or called rules. This can significantly
// speed up the retrieval process but might miss some candidates (if they are outside of the given context).
func (c3 *CodeCompletionCore) CollectCandidates(caretTokenIndex int, context ParserRuleContext) CandidatesCollection {
	c3.shortcutMap = map[int]map[int]sets.Set{}
	c3.candidates.Rules = map[int][]int{}
	c3.candidates.RulePositions = map[int][]int{}
	c3.candidates.Tokens = map[int][]int{}
	c3.statesProcessed = 0

	c3.tokenStartIndex = 0
	if context != nil {
		c3.tokenStartIndex = int(context.GetStart().GetTokenIndex())
	}
	tokenStream := c3.parser.(Parser).GetInputStream().(TokenStream)

	currentIndex := tokenStream.Index()
	tokenStream.Seek(c3.tokenStartIndex)
	c3.tokens = []Token{}

	offset := 1
	for {
		token := tokenStream.LT(offset)
		offset = offset + 1
		c3.tokens = append(c3.tokens, token)
		if token.GetTokenIndex() >= caretTokenIndex || token.GetTokenType() == TokenEOF {
			break
		}
	}
	tokenStream.Seek(currentIndex)

	callStack := arraylist.New()
	startRule := 0
	if context != nil {
		startRule = context.GetRuleIndex()
	}
	c3.processRule(c3.atn.ruleToStartState[startRule], 0, callStack, "\n")

	tokenStream.Seek(currentIndex)

	// now post-process the rule candidates and find the last occurrences
	// of each preferred rule and extract its start and end in the input stream
	for _, ruleID := range c3.preferredRules.Values() {
		shortcut, ok := c3.shortcutMap[ruleID.(int)]
		if !ok {
			continue
		}

		// select the right-most occurrence
		//final int startToken = Collections.max(shortcut.keySet());
		startToken := 0
		for k := range shortcut {
			if k > startToken {
				startToken = k
			}
		}

		endSet := shortcut[startToken]
		endToken := 0
		if endSet == nil || endSet.Size() == 0 {
			endToken = len(c3.tokens) - 1
		} else {
			// endToken = Collections.max(shortcut.get(startToken));
			endToken = 0
			for _, k := range shortcut[startToken].Values() {
				if endToken < k.(int) {
					endToken = k.(int)
				}
			}
		}

		startOffset := c3.tokens[startToken].GetStart()
		endOffset := 0
		if c3.tokens[endToken].GetTokenType() == TokenEOF {
			// if last token is EOF, include trailing whitespace
			endOffset = c3.tokens[endToken].GetStart()
		} else {
			// if last token is not EOF, limit to matching tokens which excludes trailing whitespace
			endOffset = c3.tokens[endToken-1].GetStart() + 1
		}

		ruleStartStop := []int{}
		for i := startOffset; i < endOffset; i++ {
			ruleStartStop = append(ruleStartStop, i)
		}
		c3.candidates.RulePositions[ruleID.(int)] = ruleStartStop
	}

	if c3.showResult && c3.log != nil {
		logMessage := bytes.NewBuffer([]byte{})
		fmt.Fprintf(logMessage, "States processed: %v\n", c3.statesProcessed)
		fmt.Fprintln(logMessage, "Collected rules:")
		for k, entry := range c3.candidates.Rules {
			fmt.Fprintf(logMessage, "  %d, path: ", k)
			for token := range entry {
				fmt.Fprintf(logMessage, "%s ", c3.ruleNames[token])
			}
			fmt.Fprintln(logMessage)
		}

		fmt.Fprintln(logMessage, "Collected Tokens:")
		for k, entry := range c3.candidates.Tokens {
			fmt.Fprintf(logMessage, "  %s", c3.GetDisplayName(k))
			for _, following := range entry {
				fmt.Fprintf(logMessage, " %s", c3.GetDisplayName(following))
			}
			fmt.Fprintln(logMessage)
		}
		fmt.Fprintln(c3.log, logMessage.String())
	}

	return c3.candidates
}

/**
 * Check if the predicate associated with the given transition evaluates to true.
 */
func (c3 *CodeCompletionCore) checkPredicate(transition *PredicateTransition) bool {
	return transition.getPredicate().evaluate(c3.parser, RuleContextEmpty)
}

/**
* Walks the rule chain upwards to see if that matches any of the preferred rules.
* If found, that rule is added to the collection candidates and true is returned.
 */
func (c3 *CodeCompletionCore) translateToRuleIndex(ruleStack lists.List) bool {
	if c3.preferredRules.Size() == 0 {
		return false
	}

	// Loop over the rule stack from highest to lowest rule level. This way we properly handle the higher rule
	// if it contains a lower one that is also a preferred rule.
	for i, stackEntryIF := range ruleStack.Values() {
		stackEntry := stackEntryIF.(int)
		if c3.preferredRules.Contains(stackEntry) {
			// Add the rule to our candidates list along with the current rule path,
			// but only if there isn't already an entry like that.
			path := []int{}
			for _, v := range ruleStack.Values()[0:i] {
				path = append(path, v.(int))
			}
			addNew := true
			for k, v := range c3.candidates.Rules {
				if k == stackEntry || len(v) != len(path) {
					continue
				}

				// Found an entry for this rule. Same path? If so don't add a new (duplicate) entry.
				if reflect.DeepEqual(path, v) {
					addNew = false
					break
				}
			}

			if addNew {
				c3.candidates.Rules[stackEntry] = path
				if c3.showDebugOutput && c3.log != nil {
					fmt.Fprintln(c3.log, "=====> collected: "+c3.ruleNames[stackEntry])
				}
			}
			return true
		}
	}

	return false
}

/**
 * This method follows the given transition and collects all symbols within the same rule that directly follow it
 * without intermediate transitions to other rules and only if there is a single symbol for a transition.
 */
func (c3 *CodeCompletionCore) getFollowingTokens(initialTransition Transition) []int {
	result := []int{}
	// seen := []ATNState{}
	pipeline := arraystack.New()
	pipeline.Push(initialTransition.getTarget())

	for pipeline.Size() != 0 {
		stateIF, _ := pipeline.Pop()
		state := stateIF.(ATNState)

		for _, transition := range state.GetTransitions() {
			if transition.getSerializationType() == TransitionATOM {
				if !transition.getIsEpsilon() {
					list := transition.getLabel()
					if list.length() == 1 && !c3.ignoredTokens.Contains(list.first()) {
						result = append(result, list.first())
						pipeline.Push(transition.getTarget())
					}
				} else {
					pipeline.Push(transition.getTarget())
				}
			}
		}
	}

	return result
}

/**
 * Entry point for the recursive follow set collection function.
 */
func (c3 *CodeCompletionCore) determineFollowSets(start ATNState, stop ATNState) lists.List {
	result := singlylinkedlist.New()
	seen := hashset.New()
	ruleStack := arraystack.New()

	c3.collectFollowSets(start, stop, result, seen, ruleStack)
	return result
}

/**
 * Collects possible tokens which could be matched following the given ATN state. This is essentially the same
 * algorithm as used in the LL1Analyzer class, but here we consider predicates also and use no parser rule context.
 */
func (c3 *CodeCompletionCore) collectFollowSets(s ATNState, stopState ATNState, followSets lists.List, seen sets.Set, ruleStack stacks.Stack) {
	if seen.Contains(s) {
		return
	}

	seen.Add(s)

	if s == stopState || s.GetStateType() == ATNStateRuleStop {
		is := NewIntervalSet()
		is.addOne(TokenEpsilon)

		path := arraylist.New()
		for _, v := range ruleStack.Values() {
			path.Add(v)
		}

		set := &FollowSetWithPath{
			Intervals: is,
			Path:      path,
		}
		followSets.Add(set)
		return
	}

	for _, transition := range s.GetTransitions() {
		if transition.getSerializationType() == TransitionRULE {
			ruleTransition := transition.(*RuleTransition)
			found := false
			for _, r := range ruleStack.Values() {
				if r == ruleTransition.target.GetRuleIndex() {
					found = true
					break
				}
			}
			if found {
				continue
			}

			ruleStack.Push(ruleTransition.target.GetRuleIndex())
			c3.collectFollowSets(transition.getTarget(), stopState, followSets, seen, ruleStack)
			ruleStack.Pop()
		} else if transition.getSerializationType() == TransitionPREDICATE {
			if c3.checkPredicate(transition.(*PredicateTransition)) {
				c3.collectFollowSets(transition.getTarget(), stopState, followSets, seen, ruleStack)
			}
		} else if transition.getIsEpsilon() {
			c3.collectFollowSets(transition.getTarget(), stopState, followSets, seen, ruleStack)
		} else if transition.getSerializationType() == TransitionWILDCARD {
			is := NewIntervalSet()
			is.addInterval(NewInterval(TokenMinUserTokenType, c3.atn.maxTokenType))
			path := arraylist.New()
			for _, v := range ruleStack.Values() {
				path.Add(v)
			}
			set := &FollowSetWithPath{
				Intervals: is,
				Path:      path,
			}
			followSets.Add(set)
		} else {
			label := transition.getLabel()
			if label != nil && label.length() > 0 {
				if transition.getSerializationType() == TransitionNOTSET {
					label = label.complement(TokenMinUserTokenType, c3.atn.maxTokenType)
				}
				path := arraylist.New()
				for _, v := range ruleStack.Values() {
					path.Add(v)
				}
				set := &FollowSetWithPath{
					Intervals: label,
					Path:      path,
					Following: c3.getFollowingTokens(transition),
				}
				followSets.Add(set)
			}
		}
	}
}

func (c3 *CodeCompletionCore) GetDisplayName(t int) string {
	switch t {
	case TokenEOF:
		return "<EOF>"
	case TokenEpsilon:
		return "<EPSILON>"
	default:
		if t < len(c3.vocabulary.LiteralNames) && c3.vocabulary.LiteralNames[t] != "" {
			return c3.vocabulary.LiteralNames[t]
		}

		return c3.vocabulary.SymbolicNames[t]
	}
}

/**
 * Walks the ATN for a single rule only. It returns the token stream position for each path that could be matched in this rule.
 * The result can be empty in case we hit only non-epsilon transitions that didn't match the current input or if we
 * hit the caret position.
 */
func (c3 *CodeCompletionCore) processRule(startState ATNState, tokenIndex int, callStack lists.List, indent string) sets.Set {

	// Start with rule specific handling before going into the ATN walk.

	// Check first if we've taken this path with the same input before.
	positionMap := c3.shortcutMap[startState.GetRuleIndex()]
	if positionMap == nil {
		positionMap = map[int]sets.Set{}
		c3.shortcutMap[startState.GetRuleIndex()] = positionMap
	} else {
		if _, ok := positionMap[tokenIndex]; ok {
			if c3.showDebugOutput && c3.log != nil {
				fmt.Fprintln(c3.log, "=====> shortcut")
			}
			return positionMap[tokenIndex]
		}
	}

	result := hashset.New()

	// For rule start states we determine and cache the follow set, which gives us 3 advantages:
	// 1) We can quickly check if a symbol would be matched when we follow that rule. We can so check in advance
	//    and can save us all the intermediate steps if there is no match.
	// 2) We'll have all symbols that are collectable already together when we are at the caret when entering a rule.
	// 3) We get this lookup for free with any 2nd or further visit of the same rule, which often happens
	//    in non trivial grammars, especially with (recursive) expressions and of course when invoking code completion
	//    multiple times.
	setsPerState := c3.followSetsByATN[reflect.TypeOf(c3.parser).String()]
	if setsPerState == nil {
		setsPerState = map[int]*FollowSetsHolder{}
		c3.followSetsByATN[reflect.TypeOf(c3.parser).String()] = setsPerState
	}

	followSets := setsPerState[startState.GetStateNumber()]
	if followSets == nil {
		followSets = &FollowSetsHolder{}
		setsPerState[startState.GetStateNumber()] = followSets
		stop := c3.atn.ruleToStopState[startState.GetRuleIndex()]
		followSets.Sets = c3.determineFollowSets(startState, ATNState(stop))

		// Sets are split by path to allow translating them to preferred rules. But for quick hit tests
		// it is also useful to have a set with all symbols combined.
		combined := NewIntervalSet()
		for _, set := range followSets.Sets.Values() {
			combined.addSet(set.(*FollowSetWithPath).Intervals)
		}
		followSets.Combined = combined
	}

	callStack.Add(startState.GetRuleIndex())
	currentSymbol := c3.tokens[tokenIndex].GetTokenType()

	if tokenIndex >= len(c3.tokens)-1 { // At caret?
		if c3.preferredRules.Contains(startState.GetRuleIndex()) {
			// No need to go deeper when collecting entries and we reach a rule that we want to collect anyway.
			c3.translateToRuleIndex(callStack)
		} else {
			// Convert all follow sets to either single symbols or their associated preferred rule and add
			// the result to our candidates list.
			for _, set := range followSets.Sets.Values() {
				fullPath := arraylist.New()
				fullPath.Add(set.(*FollowSetWithPath).Path.Values()...)

				if !c3.translateToRuleIndex(fullPath) {
					//                     for (int symbol : set.intervals.toList()) {
					for _, symbol := range set.(*FollowSetWithPath).Intervals.ToList() {
						if !c3.ignoredTokens.Contains(symbol) {
							if c3.showDebugOutput && c3.log != nil {
								fmt.Fprintf(c3.log, "=====> collected: %s\n", c3.GetDisplayName(symbol))
							}
							if _, ok := c3.candidates.Tokens[symbol]; !ok {
								c3.candidates.Tokens[symbol] = set.(*FollowSetWithPath).Following
							} else {
								// More than one following list for the same symbol.
								if !reflect.DeepEqual(c3.candidates.Tokens[symbol], set.(*FollowSetWithPath).Following) { // XXX js uses !=
									c3.candidates.Tokens[symbol] = []int{}
								}
							}
						} else {
							fmt.Fprintf(c3.log, "====> collection: Ignoring token: %d\n", symbol)
						}
					}
				}
			}
		}

		callStack.Remove(callStack.Size() - 1)
		return result
	} else {
		// Process the rule if we either could pass it without consuming anything (epsilon transition)
		// or if the current input symbol will be matched somewhere after this entry point.
		// Otherwise stop here.
		if !followSets.Combined.contains(TokenEpsilon) && !followSets.Combined.contains(currentSymbol) {
			callStack.Remove(callStack.Size() - 1)
			return result
		}
	}

	// The current state execution pipeline contains all yet-to-be-processed ATN states in this rule.
	// For each such state we store the token index + a list of rules that lead to it.
	statePipeline := arraystack.New()

	// Bootstrap the pipeline.
	statePipeline.Push(&PipelineEntry{State: startState, TokenIndex: tokenIndex})
outer:
	for !statePipeline.Empty() {
		currentEntryIF, _ := statePipeline.Pop()
		currentEntry := currentEntryIF.(*PipelineEntry)
		c3.statesProcessed = c3.statesProcessed + 1

		currentSymbol := c3.tokens[currentEntry.TokenIndex].GetTokenType()

		atCaret := currentEntry.TokenIndex >= len(c3.tokens)-1
		if c3.log != nil {
			c3.printDescription(indent, currentEntry.State, c3.generateBaseDescription(currentEntry.State), currentEntry.TokenIndex)
			if c3.showRuleStack {
				c3.printRuleState(callStack)
			}
		}

		switch currentEntry.State.GetStateType() {
		case ATNStateRuleStart: // Happens only for the first state in this rule, not subrules.
			indent = indent + "  "
		case ATNStateRuleStop:
			// Record the token index we are at, to report it to the caller.
			result.Add(currentEntry.TokenIndex)
			continue outer
		default:
			//no-op
		}

		transitions := currentEntry.State.GetTransitions()
		for _, transition := range transitions {
			switch transition.getSerializationType() {
			case TransitionRULE:
				endStatus := c3.processRule(transition.getTarget(), currentEntry.TokenIndex, callStack, indent)
				for _, p := range endStatus.Values() {
					statePipeline.Push(&PipelineEntry{State: transition.(*RuleTransition).followState, TokenIndex: p.(int)})
				}

			case TransitionPREDICATE:
				if c3.checkPredicate(transition.(*PredicateTransition)) {
					statePipeline.Push(&PipelineEntry{State: transition.getTarget(), TokenIndex: currentEntry.TokenIndex})
				}

			case TransitionWILDCARD:
				if atCaret {
					if c3.translateToRuleIndex(callStack) {
						is := NewIntervalSet()
						is.addInterval(NewInterval(TokenMinUserTokenType, c3.atn.maxTokenType))
						for _, token := range is.ToList() {
							if !c3.ignoredTokens.Contains(token) {
								c3.candidates.Tokens[token] = []int{}
							}
						}
					}
				} else {
					statePipeline.Push(&PipelineEntry{State: transition.getTarget(), TokenIndex: currentEntry.TokenIndex + 1})
				}

			default:
				if transition.getIsEpsilon() {
					// Jump over simple states with a single outgoing epsilon transition.
					statePipeline.Push(&PipelineEntry{State: transition.getTarget(), TokenIndex: currentEntry.TokenIndex})
					continue
				}

				set := transition.getLabel()
				if set != nil && set.length() > 0 {
					if transition.getSerializationType() == TransitionNOTSET {
						set = set.complement(TokenMinUserTokenType, c3.atn.maxTokenType)
					}
					if atCaret {
						if !c3.translateToRuleIndex(callStack) {
							list := set.ToList()
							addFollowing := len(list) == 1
							for _, symbol := range list {
								if !c3.ignoredTokens.Contains(symbol) {
									if c3.showDebugOutput && c3.log != nil {
										fmt.Fprintf(c3.log, "=====> collected: %s\n", c3.GetDisplayName(symbol))
									}
									if addFollowing {
										c3.candidates.Tokens[symbol] = c3.getFollowingTokens(transition)
									} else {
										c3.candidates.Tokens[symbol] = []int{}
									}
								} else if c3.log != nil {
									fmt.Fprintf(c3.log, "====> collected: Ignoring token: %d\n", symbol)
								}
							}
						}
					} else {
						if set.contains(currentSymbol) {
							if c3.showDebugOutput && c3.log != nil {
								fmt.Fprintf(c3.log, "=====> consumed: %s\n", c3.GetDisplayName(currentSymbol))
							}
							statePipeline.Push(&PipelineEntry{State: transition.getTarget(), TokenIndex: currentEntry.TokenIndex + 1})
						}

					}
				}
			}
		}
	}

	callStack.Remove(callStack.Size() - 1)

	// Cache the result, for later lookup to avoid duplicate walks.
	positionMap[tokenIndex] = result
	return result
}

var atnStateTypeMap = []string{
	"invalid",
	"basic",
	"rule start",
	"block start",
	"plus block start",
	"star block start",
	"token start",
	"rule stop",
	"block end",
	"star loop back",
	"star loop entry",
	"plus loop back",
	"loop end",
}

func (c3 *CodeCompletionCore) generateBaseDescription(state ATNState) string {
	stateValue := "Invalid"
	if state.GetStateNumber() != ATNStateInvalidStateNumber {
		stateValue = fmt.Sprintf("%d", state.GetStateNumber())
	}
	return "[" + stateValue + " " + atnStateTypeMap[state.GetStateType()] + "] in " + c3.ruleNames[state.GetRuleIndex()]
}

func (c3 *CodeCompletionCore) printDescription(currentIndent string, state ATNState, baseDescription string, tokenIndex int) {
	output := bytes.NewBufferString(currentIndent)

	transitionDescription := bytes.NewBufferString("")
	if c3.debugOutputWithTransitions {
		for _, transition := range state.GetTransitions() {
			labels := bytes.NewBufferString("")
			symbols := []int{}
			if transition.getLabel() != nil {
				symbols = transition.getLabel().ToList()
			}
			if len(symbols) > 2 {
				// Only print start and end symbols to avoid large lists in debug output.
				fmt.Fprintf(labels, "%s .. %s", c3.GetDisplayName(symbols[0]), c3.GetDisplayName(symbols[len(symbols)-1]))
			} else {
				for _, symbol := range symbols {
					if labels.Len() > 0 {
						labels.WriteString(", ")
					}
					labels.WriteString(c3.GetDisplayName(symbol))
				}
			}

			if labels.Len() == 0 {
				labels.WriteString("ε")
			}
			fmt.Fprintf(transitionDescription, "\n%s\t(%s) [%d %s] in %s", currentIndent, labels.String(), transition.getTarget().GetStateNumber(), atnStateTypeMap[transition.getTarget().GetStateType()], c3.ruleNames[transition.getTarget().GetRuleIndex()])
		}

		if tokenIndex >= len(c3.tokens)-1 {
			fmt.Fprintf(output, "<<%d>> ", c3.tokenStartIndex+tokenIndex)
		} else {
			fmt.Fprintf(output, "<%d> ", c3.tokenStartIndex+tokenIndex)
		}
		fmt.Fprintf(c3.log, "%s Current state: %s%s", output.String(), baseDescription, transitionDescription.String())
	}
}

func (c3 *CodeCompletionCore) printRuleState(stack lists.List) {
	if stack.Empty() {
		fmt.Println("<empty stack>")
		return
	}

	sb := bytes.NewBufferString("")
	for _, ruleIF := range stack.Values() {
		rule := ruleIF.(int)
		fmt.Fprintf(sb, "  %s\n", c3.ruleNames[rule])
	}
	fmt.Println(sb.String())
}
