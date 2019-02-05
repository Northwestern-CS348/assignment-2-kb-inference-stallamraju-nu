import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    # helper method for kb_retract that never worked!
    def prune(self):
        for f in self.facts:
            if not f.supported_by:
                self.facts.remove(f)

        for r in self.rules:
            if not r.supported_by:
                if not r.asserted:
                    self.rules.remove(r)

    def kb_retract(self, fact):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact])
        ####################################################
        # I can't figure this one out! I tried so many different iterations
        # and they all seemed like they were working but I just ran out of time :(



class InferenceEngine(object):
    def inferRuleLHSHelper(self, r, bnd):
        l = [] # create a place holder lhs array
        for i in range(len(r.lhs)): # use a for loop to go through every LHS
            l_add = instantiate(r.lhs[i],bnd) # create the instantiated statement from rule LHS's and the matched bindings
            l.append(l_add) # add the created instantiated statement into the LHS of the new inferred rule

        return l # return lhs array with everything (including first lhs)

    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        ruleLHSFirst = rule.lhs[0] # get the first element of the LHS of rule to match with
        f_s = fact.statement # get the statement of the fact given to match with
        ruleLHSLen = len(rule.lhs) # get the length of how many LHS are in rule
        bnd_betweenfr = match(ruleLHSFirst, f_s) # find all bindings between rule's first LHS and fact

        if not bnd_betweenfr: # if empty match
            return #end inference engine, there's nothing to infer
        else: # if not empty match
            s_add = instantiate(rule.rhs, bnd_betweenfr) # create either the statement to make a fact or the RHS of a rule
            if ruleLHSLen > 1: # if there is more than one LHS in rule, then we are inferring a new rule!
                r_add = Rule([[],s_add], [[fact,rule]]) # create a new inferred rule with RHS being the statement of the RHS of rule through instantiate

                r_add.lhs = self.inferRuleLHSHelper(rule, bnd_betweenfr) # get all of lhs run with instantiate

                r_add.lhs.remove(instantiate(ruleLHSFirst,bnd_betweenfr)) # remove the first LHS that was used already to infer this new rule

                fact.supports_rules.append(r_add) # say that fact supports this new inferred rule
                rule.supports_rules.append(r_add) # say that rule supports this new inferred rule

                kb.kb_add(r_add) # add the new inferred rule onto the kb

            else: # if there is only 1 LHS in rule, then we are inferring a fact since there are no more factors
                f_add = Fact(s_add, [[fact,rule]]) # create fact with statement to add from RHS from rule
                #f_add.supported_by.append(fact) # say this new fact is supported by fact
                #f_add.supported_by.append(rule) # say this new fact is supported by rule

                fact.supports_facts.append(f_add) # say that fact now supports this new fact
                rule.supports_facts.append(f_add) # say that rule now supports this new fact

                kb.kb_add(f_add) # add the new inferred fact onto the kb
