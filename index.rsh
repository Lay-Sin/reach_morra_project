'reach 0.1';

const [ isHand, ZERO, ONE, TWO, THREE, FOUR, FIVE ] = makeEnum(6);
const [ isOutcome, P1_WINS, DRAW, P2_WINS ] = makeEnum(3);

const Player = {
  ...hasRandom,
  getNumFingers: Fun([], UInt),
  getGuesses: Fun([], UInt),
  seeResult: Fun([UInt], Null),
  informTimeout: Fun([], Null),
};

const outcome = (totalFin, guess) => {
  return ((guess == totalFin) == true ? 1 : 0);
};

const result = (outcomeP1, outcomeP2) => {
  if(outcomeP1 > outcomeP2)
    return P1_WINS;
  else if (outcomeP1 < outcomeP2)
    return P2_WINS;
  else
    return DRAW;
};

export const main = Reach.App(() => {
  const p1 = Participant('p1', {
    ...Player,
    wager: UInt,
    deadline: UInt,
  });
  const p2 = Participant('p2', {
    ...Player,
    acceptWager: Fun([UInt], Null),
  });
  init();

  const informTimeout = () => {
    each([p1, p2], () => {
      interact.informTimeout();
    });
  };

  p1.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  })
  p1.publish(wager, deadline).pay(wager);
  commit();

  p2.only(() => {
    interact.acceptWager(wager);
  });
  p2.pay(wager).timeout(relativeTime(deadline), () => closeTo(p1, informTimeout));
  
  var product = DRAW;
  invariant(balance() == (2 * wager) && isOutcome(product));
  while(product == DRAW) {
    commit();
    p1.only(() => {
      const _numFinP1 = interact.getNumFingers();
      const [_commitFinP1, _saltFinP1] = makeCommitment(interact, _numFinP1);
      const commitFinP1 = declassify(_commitFinP1);

      const _guessP1 = interact.getGuesses();
      const [_commitGuessP1, _saltGuessP1] = makeCommitment(interact, _guessP1);
      const commitGuessP1 = declassify(_commitGuessP1);
    });
    p1.publish(commitFinP1, commitGuessP1).timeout(relativeTime(deadline), () => closeTo(p2, informTimeout));
    commit();

    unknowable(p2, p1(_guessP1, _numFinP1, _saltFinP1, _saltGuessP1));

    p2.only(() => {
      const numFinP2 = declassify(interact.getNumFingers());
      const guessP2 = declassify(interact.getGuesses());
    });
    p2.publish(numFinP2, guessP2).timeout(relativeTime(deadline), () => closeTo(p1, informTimeout));
    commit();

    p1.only(() => {
      const saltFinP1 = declassify(_saltFinP1);
      const numFinP1 = declassify(_numFinP1);
      const saltGuessP1 = declassify(_saltGuessP1);
      const guessP1 = declassify(_guessP1);
    })
    p1.publish(saltFinP1, numFinP1, saltGuessP1, guessP1).timeout(relativeTime(deadline), () => closeTo(p2, informTimeout));
    checkCommitment(commitFinP1, saltFinP1, numFinP1);
    checkCommitment(commitGuessP1, saltGuessP1, guessP1);
    
    const totalFin = numFinP1 + numFinP2;
    product = result(outcome(totalFin, guessP1), outcome(totalFin, guessP2));
    continue;
  }

  assert(product == P1_WINS || product == P2_WINS)
  transfer(2 * wager).to((product == P1_WINS) ? p1 : p2);
  commit();

  each([p1, p2], () => {
    interact.seeResult(product);
  });
});
