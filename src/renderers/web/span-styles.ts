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

import AnimationCollection = require("./animation-collection");
import domParser = require("./dom-parser");

import WebRenderer = require("./renderer");

import RendererSettings = require("../settings");

import parts = require("../../parts/index");
import Color = parts.Color;

import Style = require("../../types/style");
import Dialogue = require("../../types/dialogue");

import map = require("../../utility/map");

///<reference path="./web-references.d.ts" />

/**
 * This class represents the style attribute of a span.
 * As a Dialogue's div is rendered, individual parts are added to span's, and this class is used to maintain the style attribute of those.
 *
 * @param {!libjass.renderers.NullRenderer} renderer The renderer that this set of styles is associated with
 * @param {!libjass.Dialogue} dialogue The Dialogue that this set of styles is associated with
 * @param {number} scaleX The horizontal scaling of the subtitles
 * @param {number} scaleY The vertical scaling of the subtitles
 * @param {!libjass.renderers.RendererSettings} settings The renderer settings
 * @param {!HTMLDivElement} fontSizeElement A <div> element to measure font sizes with
 * @param {!SVGDefsElement} svgDefsElement An SVG <defs> element to append filter definitions to
 */
class SpanStyles {
	private static _fontSizeCache: map.Map<string, map.Map<number, number>> = new map.Map<string, map.Map<number, number>>();

	private _id: string;
	private _defaultStyle: Style;

	private _italic: boolean;
	private _bold: Object;
	private _underline: boolean;
	private _strikeThrough: boolean;

	private _outlineWidth: number;
	private _outlineHeight: number;

	private _shadowDepthX: number;
	private _shadowDepthY: number;

	private _fontName: string;
	private _fontSize: number;

	private _fontScaleX: number;
	private _fontScaleY: number;

	private _letterSpacing: number;

	private _rotationX: number;
	private _rotationY: number;
	private _rotationZ: number;

	private _skewX: number;
	private _skewY: number;

	private _primaryColor: Color;
	private _secondaryColor: Color;
	private _outlineColor: Color;
	private _shadowColor: Color;

	private _primaryAlpha: number;
	private _secondaryAlpha: number;
	private _outlineAlpha: number;
	private _shadowAlpha: number;

	private _blur: number;
	private _gaussianBlur: number;

	private _nextFilterId = 0;

	constructor(renderer: WebRenderer, dialogue: Dialogue, private _scaleX: number, private _scaleY: number, private _settings: RendererSettings, private _fontSizeElement: HTMLDivElement, private _svgDefsElement: SVGDefsElement) {
		this._id = `${ renderer.id }-${ dialogue.id }`;
		this._defaultStyle = dialogue.style;

		this.reset(null);
	}

	/**
	 * Resets the styles to the defaults provided by the argument.
	 *
	 * @param {libjass.Style} newStyle The new defaults to reset the style to. If null, the styles are reset to the default style of the Dialogue.
	 */
	reset(newStyle: Style): void {
		if (newStyle === undefined || newStyle === null) {
			newStyle = this._defaultStyle;
		}

		this.italic = newStyle.italic;
		this.bold = newStyle.bold;
		this.underline = newStyle.underline;
		this.strikeThrough = newStyle.strikeThrough;

		this.outlineWidth = newStyle.outlineThickness;
		this.outlineHeight = newStyle.outlineThickness;

		this.shadowDepthX = newStyle.shadowDepth;
		this.shadowDepthY = newStyle.shadowDepth;

		this.fontName = newStyle.fontName;
		this.fontSize = newStyle.fontSize;

		this.fontScaleX = newStyle.fontScaleX;
		this.fontScaleY = newStyle.fontScaleY;

		this.letterSpacing = newStyle.letterSpacing;

		this._rotationX = null;
		this._rotationY = null;
		this._rotationZ = newStyle.rotationZ;

		this._skewX = null;
		this._skewY = null;

		this.primaryColor = newStyle.primaryColor;
		this.secondaryColor = newStyle.secondaryColor;
		this.outlineColor = newStyle.outlineColor;
		this.shadowColor = newStyle.shadowColor;

		this.primaryAlpha = null;
		this.secondaryAlpha = null;
		this.outlineAlpha = null;
		this.shadowAlpha = null;

		this.blur = null;
		this.gaussianBlur = null;
	}

	/**
	 * Sets the style attribute on the given span element.
	 *
	 * @param {!HTMLSpanElement} span
	 * @param {!AnimationCollection} animationCollection
	 * @param {!HTMLStyleElement} animationStyleElement
	 * @return {!HTMLSpanElement} The resulting <span> with the CSS styles applied. This may be a wrapper around the input <span> if the styles were applied using SVG filters.
	 */
	setStylesOnSpan(span: HTMLSpanElement, animationCollection: AnimationCollection, animationStyleElement: HTMLStyleElement): HTMLSpanElement {
		var isTextOnlySpan = span.childNodes[0] instanceof Text;

		var fontStyleOrWeight = "";
		if (this._italic) {
			fontStyleOrWeight += "italic ";
		}
		if (this._bold === true) {
			fontStyleOrWeight += "bold ";
		}
		else if (this._bold !== false) {
			fontStyleOrWeight += this._bold + " ";
		}
		var fontSize: string;
		if (isTextOnlySpan) {
			fontSize = (this._scaleY * SpanStyles._getFontSize(this._fontName, this._fontSize * this._fontScaleY, this._fontSizeElement)).toFixed(3);
		}
		else {
			fontSize = (this._scaleY * SpanStyles._getFontSize(this._fontName, this._fontSize, this._fontSizeElement)).toFixed(3);
		}
		var lineHeight = (this._scaleY * this._fontSize).toFixed(3);
		span.style.font = `${ fontStyleOrWeight }${ fontSize }px/${ lineHeight }px "${ this._fontName }"`;

		var textDecoration = "";
		if (this._underline) {
			textDecoration = "underline";
		}
		if (this._strikeThrough) {
			textDecoration += " line-through";
		}
		span.style.textDecoration = textDecoration.trim();

		var transform = "";
		if (isTextOnlySpan) {
			if (this._fontScaleY !== this._fontScaleX) {
				transform += `scaleY(${ (this._fontScaleY / this._fontScaleX).toFixed(3) }) `;
			}
		}
		else {
			if (this._fontScaleX !== 1) {
				transform += `scaleX(${ this._fontScaleX }) `;
			}
			if (this._fontScaleY !== 1) {
				transform += `scaleY(${ this._fontScaleY }) `;
			}
		}
		if (this._rotationY !== null) {
			transform += `rotateY(${ this._rotationY }deg) `;
		}
		if (this._rotationX !== null) {
			transform += `rotateX(${ this._rotationX }deg) `;
		}
		if (this._rotationZ !== 0) {
			transform += `rotateZ(${ -1 * this._rotationZ }deg) `;
		}
		if (this._skewX !== null || this._skewY !== null) {
			var skewX = SpanStyles._valueOrDefault(this._skewX, 0);
			var skewY = SpanStyles._valueOrDefault(this._skewY, 0);
			transform += `matrix(1, ${ skewY }, ${ skewX }, 1, 0, 0) `;
		}
		if (transform !== "") {
			span.style.webkitTransform = transform;
			span.style.webkitTransformOrigin = "50% 50%";
			span.style.transform = transform;
			span.style.transformOrigin = "50% 50%";
			span.style.display = "inline-block";
		}

		span.style.letterSpacing = `${ (this._scaleX * this._letterSpacing).toFixed(3) }px`;

		var primaryColor = this._primaryColor.withAlpha(this._primaryAlpha);
		span.style.color = primaryColor.toString();

		var outlineColor = this._outlineColor.withAlpha(this._outlineAlpha);

		var outlineWidth = this._scaleX * this._outlineWidth;
		var outlineHeight = this._scaleY * this._outlineHeight;

		var outlineFilter = '';
		var blurFilter = '';

		if (this._settings.enableSvg) {
			var filterId = `svg-filter-${ this._id }-${ this._nextFilterId++ }`;

			if (outlineWidth > 0 || outlineHeight > 0) {
				/* Construct an elliptical border by merging together many rectangles. The border is creating using dilate morphology filters, but these only support
				 * generating rectangles.   http://lists.w3.org/Archives/Public/public-fx/2012OctDec/0003.html
				 */

				var mergeOutlinesFilter = '';

				var outlineNumber = 0;

				var increment = (!this._settings.preciseOutlines && this._gaussianBlur > 0) ? this._gaussianBlur : 1;

				((addOutline: (x: number, y: number) => void) => {
					if (outlineWidth <= outlineHeight) {
						if (outlineWidth > 0) {
							for (var x = 0; x <= outlineWidth; x += increment) {
								addOutline(x, outlineHeight / outlineWidth * Math.sqrt(outlineWidth * outlineWidth - x * x));
							}
							if (x !== outlineWidth + increment) {
								addOutline(outlineWidth, 0);
							}
						}
						else {
							addOutline(0, outlineHeight);
						}
					}
					else {
						if (outlineHeight > 0) {
							for (var y = 0; y <= outlineHeight; y += increment) {
								addOutline(outlineWidth / outlineHeight * Math.sqrt(outlineHeight * outlineHeight - y * y), y);
							}
							if (y !== outlineHeight + increment) {
								addOutline(0, outlineHeight);
							}
						}
						else {
							addOutline(outlineWidth, 0);
						}
					}
				})((x: number, y: number): void => {
					outlineFilter +=
`	<feMorphology in="SourceAlpha" operator="dilate" radius="${ x.toFixed(3) } ${ y.toFixed(3) }" result="outline${ outlineNumber }" />
`;

					mergeOutlinesFilter +=
`		<feMergeNode in="outline${ outlineNumber }" />
`;

					outlineNumber++;
				});

				outlineFilter +=
`	<feMerge result="outline">
${ mergeOutlinesFilter }
</feMerge>
<feFlood flood-color="${ outlineColor.toString() }" />
<feComposite operator="in" in2="outline" />
`;
			}

			if (this._gaussianBlur > 0) {
				blurFilter +=
`	<feGaussianBlur stdDeviation="${ this._gaussianBlur }" />
`;
			}
			for (var i = 0; i < this._blur; i++) {
				blurFilter +=
`	<feConvolveMatrix kernelMatrix="1 2 1 2 4 2 1 2 1" edgeMode="none" />
`;
			}
		}
		else {
			if (outlineWidth > 0 || outlineHeight > 0) {
				var outlineCssString = "";

				((addOutline: (x: number, y: number) => void) => {
					for (var x = 0; x <= outlineWidth; x++) {
						var maxY = (outlineWidth === 0) ? outlineHeight : outlineHeight * Math.sqrt(1 - ((x * x) / (outlineWidth * outlineWidth)));
						for (var y = 0; y <= maxY; y++) {
							addOutline(x, y);

							if (x !== 0) {
								addOutline(-x, y);
							}

							if (y !== 0) {
								addOutline(x, -y);
							}

							if (x !== 0 && y !== 0) {
								addOutline(-x, -y);
							}
						}
					}
				})((x: number, y: number): void => {
					outlineCssString += `, ${ outlineColor.toString() } ${ x }px ${ y }px ${ this._gaussianBlur.toFixed(3) }px`;
				});

				span.style.textShadow = outlineCssString.substr(", ".length);
			}
		}

		var filterWrapperSpan = document.createElement("span");
		filterWrapperSpan.appendChild(span);

		if (outlineFilter !== '' || blurFilter !== '') {
			var filterString =
`<filter xmlns="http://www.w3.org/2000/svg" id="${ filterId }" x="-50%" width="200%" y="-50%" height="200%">
${ outlineFilter }
${ blurFilter }
<feMerge>
	<feMergeNode />
	<feMergeNode in="SourceGraphic" />
</feMerge>
</filter>
`;

			var filterElement = domParser.parseFromString(filterString, "image/svg+xml").childNodes[0];

			this._svgDefsElement.appendChild(filterElement);

			filterWrapperSpan.style.webkitFilter = `url("#${ filterId }")`;
			filterWrapperSpan.style.filter = `url("#${ filterId }")`;
		}

		if (this._shadowDepthX !== 0 || this._shadowDepthY !== 0) {
			var shadowColor = this._shadowColor.withAlpha(this._shadowAlpha);
			var shadowCssString = `${ shadowColor.toString() } ${ (this._shadowDepthX * this._scaleX / this._fontScaleX).toFixed(3) }px ${ (this._shadowDepthY * this._scaleY / this._fontScaleY).toFixed(3) }px 0px`;
			if (span.style.textShadow === "") {
				span.style.textShadow = shadowCssString;
			}
			else {
				span.style.textShadow += ", " + shadowCssString;
			}
		}

		if (this._rotationX !== 0 || this._rotationY !== 0) {
			// Perspective needs to be set on a "transformable element"
			filterWrapperSpan.style.display = "inline-block";
		}

		animationStyleElement.appendChild(document.createTextNode(animationCollection.cssText));

		span.style.webkitAnimation = animationCollection.animationStyle;
		span.style.animation = animationCollection.animationStyle;

		return filterWrapperSpan;
	}

	/**
	 * @return {!HTMLBRElement}
	 */
	makeNewLine(): HTMLBRElement {
		var result = document.createElement("br");
		result.style.lineHeight = `${ (this._scaleY * this._fontSize).toFixed(3) }px`;
		return result;
	}

	/**
	 * Sets the italic property. null defaults it to the default style's value.
	 *
	 * @type {?boolean}
	 */
	set italic(value: boolean) {
		this._italic = SpanStyles._valueOrDefault(value, this._defaultStyle.italic);
	}

	/**
	 * Sets the bold property. null defaults it to the default style's value.
	 *
	 * @type {(?number|?boolean)}
	 */
	set bold(value: Object) {
		this._bold = SpanStyles._valueOrDefault(value, this._defaultStyle.bold);
	}

	/**
	 * Sets the underline property. null defaults it to the default style's value.
	 *
	 * @type {?boolean}
	 */
	set underline(value: boolean) {
		this._underline = SpanStyles._valueOrDefault(value, this._defaultStyle.underline);
	}

	/**
	 * Sets the strike-through property. null defaults it to the default style's value.
	 *
	 * @type {?boolean}
	 */
	set strikeThrough(value: boolean) {
		this._strikeThrough = SpanStyles._valueOrDefault(value, this._defaultStyle.strikeThrough);
	}

	/**
	 * Sets the outline width property. null defaults it to the style's original outline width value.
	 *
	 * @type {?number}
	 */
	set outlineWidth(value: number) {
		this._outlineWidth = SpanStyles._valueOrDefault(value, this._defaultStyle.outlineThickness);
	}

	/**
	 * Sets the outline height property. null defaults it to the style's original outline height value.
	 *
	 * @type {?number}
	 */
	set outlineHeight(value: number) {
		this._outlineHeight = SpanStyles._valueOrDefault(value, this._defaultStyle.outlineThickness);
	}

	/**
	 * Sets the outline width property. null defaults it to the style's original shadow depth X value.
	 *
	 * @type {?number}
	 */
	set shadowDepthX(value: number) {
		this._shadowDepthX = SpanStyles._valueOrDefault(value, this._defaultStyle.shadowDepth);
	}

	/**
	 * Sets the shadow height property. null defaults it to the style's original shadow depth Y value.
	 *
	 * @type {?number}
	 */
	set shadowDepthY(value: number) {
		this._shadowDepthY = SpanStyles._valueOrDefault(value, this._defaultStyle.shadowDepth);
	}

	/**
	 * Sets the blur property. null defaults it to 0.
	 *
	 * @type {?number}
	 */
	set blur(value: number) {
		this._blur = SpanStyles._valueOrDefault(value, 0);
	}

	/**
	 * Sets the Gaussian blur property. null defaults it to 0.
	 *
	 * @type {?number}
	 */
	set gaussianBlur(value: number) {
		this._gaussianBlur = SpanStyles._valueOrDefault(value, 0);
	}

	/**
	 * Sets the font name property. null defaults it to the default style's value.
	 *
	 * @type {?string}
	 */
	set fontName(value: string) {
		this._fontName = SpanStyles._valueOrDefault(value, this._defaultStyle.fontName);
	}

	/**
	 * Sets the font size property. null defaults it to the default style's value.
	 *
	 * @type {?number}
	 */
	set fontSize(value: number) {
		this._fontSize = SpanStyles._valueOrDefault(value, this._defaultStyle.fontSize);
	}

	/**
	 * Sets the horizontal font scaling property. null defaults it to the default style's value.
	 *
	 * @type {?number}
	 */
	set fontScaleX(value: number) {
		this._fontScaleX = SpanStyles._valueOrDefault(value, this._defaultStyle.fontScaleX);
	}

	/**
	 * Sets the vertical font scaling property. null defaults it to the default style's value.
	 *
	 * @type {?number}
	 */
	set fontScaleY(value: number) {
		this._fontScaleY = SpanStyles._valueOrDefault(value, this._defaultStyle.fontScaleY);
	}

	/**
	 * Sets the letter spacing property. null defaults it to the default style's value.
	 *
	 * @type {?number}
	 */
	set letterSpacing(value: number) {
		this._letterSpacing = SpanStyles._valueOrDefault(value, this._defaultStyle.letterSpacing);
	}

	/**
	 * Sets the X-axis rotation property.
	 *
	 * @type {?number}
	 */
	set rotationX(value: number) {
		this._rotationX = value;
	}

	/**
	 * Sets the Y-axis rotation property.
	 *
	 * @type {?number}
	 */
	set rotationY(value: number) {
		this._rotationY = value;
	}

	/**
	 * Sets the Z-axis rotation property.
	 *
	 * @type {?number}
	 */
	set rotationZ(value: number) {
		this._rotationZ = SpanStyles._valueOrDefault(value, this._defaultStyle.rotationZ);
	}

	/**
	 * Sets the X-axis skew property.
	 *
	 * @type {?number}
	 */
	set skewX(value: number) {
		this._skewX = value;
	}

	/**
	 * Sets the Y-axis skew property.
	 *
	 * @type {?number}
	 */
	set skewY(value: number) {
		this._skewY = value;
	}

	/**
	 * Gets the primary color property.
	 *
	 * @type {!libjass.Color}
	 */
	get primaryColor(): Color {
		return this._primaryColor;
	}

	/**
	 * Sets the primary color property. null defaults it to the default style's value.
	 *
	 * @type {libjass.Color}
	 */
	set primaryColor(value: Color) {
		this._primaryColor = SpanStyles._valueOrDefault(value, this._defaultStyle.primaryColor);
	}

	/**
	 * Gets the secondary color property.
	 *
	 * @type {!libjass.Color}
	 */
	get secondaryColor(): Color {
		return this._secondaryColor;
	}

	/**
	 * Sets the secondary color property. null defaults it to the default style's value.
	 *
	 * @type {libjass.Color}
	 */
	set secondaryColor(value: Color) {
		this._secondaryColor = SpanStyles._valueOrDefault(value, this._defaultStyle.secondaryColor);
	}

	/**
	 * Sets the outline color property. null defaults it to the default style's value.
	 *
	 * @type {libjass.Color}
	 */
	set outlineColor(value: Color) {
		this._outlineColor = SpanStyles._valueOrDefault(value, this._defaultStyle.outlineColor);
	}

	/**
	 * Sets the shadow color property. null defaults it to the default style's value.
	 *
	 * @type {libjass.Color}
	 */
	set shadowColor(value: Color) {
		this._shadowColor = SpanStyles._valueOrDefault(value, this._defaultStyle.shadowColor);
	}

	/**
	 * Gets the primary alpha property.
	 *
	 * @type {?number}
	 */
	get primaryAlpha(): number {
		return this._primaryAlpha;
	}

	/**
	 * Sets the primary alpha property.
	 *
	 * @type {?number}
	 */
	set primaryAlpha(value: number) {
		this._primaryAlpha = value;
	}

	/**
	 * Gets the secondary alpha property.
	 *
	 * @type {?number}
	 */
	get secondaryAlpha(): number {
		return this._secondaryAlpha;
	}

	/**
	 * Sets the secondary alpha property.
	 *
	 * @type {?number}
	 */
	set secondaryAlpha(value: number) {
		this._secondaryAlpha = value;
	}

	/**
	 * Sets the outline alpha property.
	 *
	 * @type {?number}
	 */
	set outlineAlpha(value: number) {
		this._outlineAlpha = value;
	}

	/**
	 * Sets the shadow alpha property.
	 *
	 * @type {?number}
	 */
	set shadowAlpha(value: number) {
		this._shadowAlpha = value;
	}

	private static _valueOrDefault = <T>(newValue: T, defaultValue: T): T => ((newValue !== null) ? newValue : defaultValue);

	/**
	 * @param {string} fontFamily
	 * @param {number} lineHeight
	 * @param {!HTMLDivElement} fontSizeElement
	 * @return {number}
	 */
	private static _getFontSize(fontFamily: string, lineHeight: number, fontSizeElement: HTMLDivElement): number {
		var existingFontSizeMap = SpanStyles._fontSizeCache.get(fontFamily);
		if (existingFontSizeMap === undefined) {
			SpanStyles._fontSizeCache.set(fontFamily, existingFontSizeMap = new map.Map<number, number>());
		}

		var existingFontSize = existingFontSizeMap.get(lineHeight);
		if (existingFontSize === undefined) {
			fontSizeElement.style.fontFamily = fontFamily;
			fontSizeElement.style.fontSize = `${ lineHeight }px`;
			existingFontSizeMap.set(lineHeight, existingFontSize = lineHeight * lineHeight / fontSizeElement.offsetHeight);
		}

		return existingFontSize;
	}
}

export = SpanStyles;
