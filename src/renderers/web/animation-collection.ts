/**
 * libjass
 *
 * https://github.com/Arnavion/libjass
 *
 * Copyright 2013 Arnav Singh
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *    http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import Keyframe = require("./keyframe");

import NullRenderer = require("../null");

import map = require("../../utility/map");

/**
 * This class represents a collection of animations. Each animation contains one or more keyframes.
 * The collection can then be converted to a CSS3 representation.
 *
 * @param {!libjass.renderers.NullRenderer} renderer The renderer that this collection is associated with
 */
class AnimationCollection {
	private static _nextId: number = 0;

	private _id: string;
	private _rate: number;

	private _cssText: string = "";
	private _animationStyle: string = "";
	private _animationDelays: map.Map<string, number> = new map.Map<string, number>();
	private _numAnimations: number = 0;

	constructor(renderer: NullRenderer) {
		this._id = `${ renderer.id }-${ AnimationCollection._nextId++ }`;
		this._rate = renderer.clock.rate;
	}

	/**
	 * This string contains the animation definitions and should be inserted into a <style> element.
	 *
	 * @type {string}
	 */
	get cssText(): string {
		return this._cssText;
	}

	/**
	 * This string should be set as the "animation" CSS property of the target element.
	 *
	 * @type {string}
	 */
	get animationStyle(): string {
		return this._animationStyle;
	}

	/**
	 * This array should be used to set the "animation-delay" CSS property of the target element.
	 *
	 * @type {!Array.<number>}
	 */
	get animationDelays(): map.Map<string, number> {
		return this._animationDelays;
	}

	/**
	 * Add an animation to this collection. The given keyframes together make one animation.
	 *
	 * @param {string} timingFunction One of the acceptable values for the "animation-timing-function" CSS property
	 * @param {!Array.<!libjass.renderers.Keyframe>} keyframes
	 */
	add(timingFunction: string, keyframes: Keyframe[]): void {
		var start: number = null;
		var end: number = null;

		var ruleCssText = "";

		keyframes.forEach(keyframe => {
			if (start === null) {
				start = keyframe.time;
			}

			end = keyframe.time;
		});

		keyframes.forEach(keyframe => {
			ruleCssText +=
`	${ (100 * ((end - start === 0) ? 1 : ((keyframe.time - start) / (end - start)))).toFixed(3) }% {
`;

			keyframe.properties.forEach((value, name) => {
				ruleCssText +=
`		${ name }: ${ value };
`;
			});

			ruleCssText +=
`	}
`;
		});

		var animationName = `animation-${ this._id }-${ this._numAnimations++ }`;

		this._cssText +=
`@-webkit-keyframes ${ animationName } {
${ ruleCssText }
}

@keyframes ${ animationName } {
${ ruleCssText }
}

`;

		if (this._animationStyle !== "") {
			this._animationStyle += ",";
		}

		this._animationStyle += `${ animationName } ${ ((end - start) / this._rate).toFixed(3) }s ${ timingFunction }`;
		this._animationDelays.set(animationName, start);
	}
}

export = AnimationCollection;
